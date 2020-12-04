package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import java.util.Arrays;

public class UnresolvedNode extends Node {
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
  @Override public Node ideal(GVNGCM gvn, int level) {
    if( _defs._len < 2 )               // One function, consumer should treat as a copy
      throw com.cliffc.aa.AA.unimpl(); // Should collapse
    // Back-to-back Unresolved collapse (happens due to inlining)
    boolean progress=false;
    for( int i=0; i<_defs._len; i++ ) {
      if( in(i) instanceof UnresolvedNode ) {
        progress = true;
        Node u = in(i);
// TODO: folding a primitive Unresolved, instead probably need to make a new one...
        for( int j=0; j<u._defs._len; j++ )
          add_def(u.in(j));
        set_def(i,pop(),gvn);
      }
    }
    return progress ? this : null;
  }

  // Required property for value():
  // ANY >= value(ANY) >= value(other) >= value(ALL) >= ALL
  @Override public Type value(GVNGCM.Mode opt_mode) {
    // Freeze after GVN - only still around for errors
    if( opt_mode == GVNGCM.Mode.PesiCG ) return val();
    boolean lifting = opt_mode!=GVNGCM.Mode.Opto;
    Type t   = lifting ? Type.ANY : Type.ALL;
    for( Node def : _defs ) {
      Type td = def.val();
      if( !(td instanceof TypeFunPtr) ) return td.oob();
      TypeFunPtr tfp = (TypeFunPtr)td;
      if( tfp.above_center() == lifting ) tfp = tfp.dual();
      t = lifting ? t.meet(tfp) : t.join(tfp);
    }
    return t;
  }

  // Validate same name, operator-precedence and thunking
  private void add_def_unresolved( FunPtrNode ptr ) {
    FunPtrNode ptr0 = (FunPtrNode)in(0);
    assert Util.eq(ptr0.fun()._name,ptr.fun()._name);
    // Actually, equal op_prec & thunk only for binary ops
    assert ptr0.fun()._op_prec  == ptr.fun()._op_prec;
    assert ptr0.fun()._thunk_rhs== ptr.fun()._thunk_rhs;
    add_def(ptr);
  }

  // Filter out all the wrong-arg-count functions
  public Node filter( GVNGCM gvn, int nargs ) {
    Node x = null;
    for( Node epi : _defs ) {
      FunNode fun =  ((FunPtrNode)epi).fun();
      // User-nargs are user-visible #arguments.
      // Fun-nargs include the ctrl, display & memory, hence the +2.
      if( fun.nargs() != nargs+3 ) continue;
      if( x == null ) x = epi;
      else if( x instanceof UnresolvedNode ) ((UnresolvedNode)x).add_def_unresolved((FunPtrNode)epi);
      else x = new UnresolvedNode(_bad,x,epi);
    }
    return x instanceof UnresolvedNode ? gvn.xform(x) : x;
  }

  // Return a funptr for this fidx.
  FunPtrNode find_fidx( int fidx ) {
    for( Node n : _defs )
      if( ((FunPtrNode)n).ret()._fidx==fidx )
        return (FunPtrNode)n;
    return null;
  }

  // Compute local contribution of use liveness to this def.
  // If pre-GCP, same as value() above, use the conservative answer.
  // During GCP, this will resolve so use the optimistic answer.
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( !opt_mode._CG ) return super.live_use(opt_mode,def);
    if( !(def instanceof FunPtrNode) ) return _live;
    // If any Call has resolved to this def, its alive.
    // If not a Call, must assume it props to some unknown Call and is alive.
    int dfidx = ((FunPtrNode)def).ret()._fidx;
    for( Node call : _uses )
      if( !(call instanceof CallNode) ||
          ((CallNode)call).live_use_call(dfidx) != TypeMem.DEAD )
        return _live;
    // Only call users, and no call wants this def.
    return TypeMem.DEAD;
  }

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
