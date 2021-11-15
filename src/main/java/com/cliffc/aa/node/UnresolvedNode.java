package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import java.util.Arrays;

import static com.cliffc.aa.AA.ARG_IDX;

public class UnresolvedNode extends UnOrFunPtrNode {
  private final Parse _bad;
  UnresolvedNode( Parse bad, Node... funs ) { super(OP_UNR,funs); _bad = bad; }
  @Override public String xstr() {
    if( is_dead() ) return "DEAD";
    if( in(0) instanceof FunPtrNode ) {
      FunPtrNode fptr = (FunPtrNode)in(0);
      FunNode fun = fptr.xfun();
      return "Unr:"+(fun==null ? "null" : fun.xstr());
    }
    return "Unr???";
  }
  @Override public Node ideal_reduce() {
    if( _defs._len < 2 )               // One function, consumer should treat as a copy
      return in(0);                    // Collapse
    // Back-to-back Unresolved collapse (happens due to inlining)
    boolean progress=false;
    for( int i=0; i<_defs._len; i++ ) {
      if( in(i) instanceof UnresolvedNode ) {
        progress = true;
        Node u = in(i);
// TODO: folding a primitive Unresolved, instead probably need to make a new one...
        for( int j=0; j<u._defs._len; j++ )
          add_def(u.in(j));
        set_def(i,pop());
      }
      assert in(i) instanceof FunPtrNode;
      if( in(i).in(0)==null )
        { progress = true; remove(i--); }
    }
    return progress ? this : null;
  }

  // Required property for value():
  // ANY >= value(ANY) >= value(other) >= value(ALL) >= ALL
  @Override public Type value(GVNGCM.Mode opt_mode) {
    switch( opt_mode ) {
    case PesiCG:
      return _val; // Freeze after GVN - only still around for errors
    case Parse:
    case PesiNoCG:
      Type t = Type.ANY;
      for( Node def : _defs ) {
        Type td = def._val;
        if( !(td instanceof TypeFunPtr) ) return td.oob();
        t = t.meet(td);
      }
      return t;
    case Opto:
      // If all inputs are TFPs, result is a high choice of TFPs, plus the
      // normal join over displays.
      BitsFun fidxs = BitsFun.EMPTY;
      Type tdsp = Type.ALL, tret = Type.ALL;
      int nargs = -1;
      for( Node fptr : _defs ) {
        Type td = fptr._val;
        if( !(td instanceof TypeFunPtr) ) return td.oob();
        TypeFunPtr tfp = (TypeFunPtr)td;
        fidxs = fidxs.meet((tfp.above_center() ? tfp.dual() : tfp)._fidxs);
        tdsp = tdsp.join(tfp._dsp);
        tret = tret.join(tfp._ret);
        nargs = tfp.nargs();
      }
      if( fidxs.abit()!= -1 )
        return TypeFunPtr.make(fidxs,nargs,tdsp,tret);
      return TypeFunPtr.make(fidxs.dual(),nargs,tdsp,tret);
    default: throw com.cliffc.aa.AA.unimpl();
    }
  }

  // An UnresolvedNode is its own Leaf, because it might gather fairly unrelated
  // functions - such as integer-add vs string-add, or the 1-argument leading
  // '+' operator vs the more expected binop.
  @Override public boolean unify( WorkNode work ) {
    // Giant assert that all inputs are all Fun, ignoring errors.
    for( Node n : _defs ) {
      TV2 tv = n.tvar();
      assert tv.is_err() || tv.is_fun() || tv.is_leaf();
    }
    return false;
  }

  // Validate same name, operator-precedence and thunking
  private void add_def_unresolved( FunPtrNode ptr ) {
    if( _defs._len>0 ) {
      FunPtrNode ptr0 = (FunPtrNode) in(0);
      assert Util.eq(ptr0._name, ptr._name);
      // Actually, equal op_prec & thunk only for binary ops
      assert ptr0.fun()._op_prec == ptr.fun()._op_prec || ptr0.nargs()== AA.ARG_IDX+1; // Either a uniop, or same precedence
      assert ptr0.fun()._thunk_rhs == ptr.fun()._thunk_rhs;
    }
    add_def(ptr);
  }

  // Filter out all the wrong-arg-count functions from Parser.
  @Override public UnOrFunPtrNode filter( int nargs ) {
    UnOrFunPtrNode x = null;
    for( Node epi : _defs ) {
      FunPtrNode fptr = (FunPtrNode)epi;
      // User-nargs are user-visible #arguments.
      // Fun-nargs include the ctrl, display & memory, hence the +ARG_IDX.
      if( fptr.nargs() != ARG_IDX+nargs ) continue;
      if( fptr.op_prec()==0 ) continue; // Balanced op
      if( x == null ) x = fptr.keep();
      else if( x instanceof UnresolvedNode ) ((UnresolvedNode)x).add_def_unresolved(fptr);
      else x = new UnresolvedNode(_bad,x.unkeep(),fptr).keep();
    }
    return x==null ? null : (UnOrFunPtrNode)Env.GVN.xform(x.unkeep());
  }

  // Return a funptr for this fidx.
  FunPtrNode find_fidx( int fidx ) {
    for( Node n : _defs )
      if( ((FunPtrNode)n).ret()._fidx==fidx )
        return (FunPtrNode)n;
    return null;
  }

  // Same NARGS across all defs
  @Override public int nargs() { return funptr().nargs(); }
  @Override public FunPtrNode funptr() { return (FunPtrNode)_defs.at(0); }
  @Override public UnresolvedNode unk() { return this; }

  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }
  @Override public int hashCode() { return super.hashCode()+(_bad==null ? 0 : _bad.hashCode()); }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _bad==((UnresolvedNode)o)._bad;
  }
  // Make a copy with an error message
  public UnresolvedNode copy(Parse bad) {
    return new UnresolvedNode(bad,Arrays.copyOf(_defs._es,_defs._len));
  }

  // Choice of typically primitives, all of which are pure.
  // Instead of returning the pre-call memory on true, returns self.
  @Override Node is_pure_call() {
    for( Node fun : _defs )
      if( fun.is_pure_call() == null )
        return null;
    return this;                // Yes, all choices are pure
  }
}
