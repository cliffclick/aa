package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeMem;

import java.util.Arrays;

public class UnresolvedNode extends Node {
  private Parse _bad;
  UnresolvedNode( Parse bad, Node... funs ) { super(OP_UNR,funs); _bad = bad; }
  @Override String xstr() {
    if( is_dead() ) return "DEAD";
    if( in(0) instanceof FunPtrNode ) {
      FunPtrNode fptr = (FunPtrNode)in(0);
      FunNode fun = fptr.fun();
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
        for( int j=0; j<u._defs._len; j++ )
          add_def(u.in(j));
        set_def(i,pop(),gvn);
      }
    }
    return progress ? this : null;
  }

  @Override public TypeFunPtr value(GVNGCM gvn) {
    final TypeFunPtr GF = TypeFunPtr.GENERIC_FUNPTR;
    if( gvn._opt_mode < 2 ) { // parse or 1st iter: assume all can happen, and hope to resolve to lift
      TypeFunPtr t = GF.dual();
      for( Node def : _defs ) {
        Type td = gvn.type(def);
        if( !(td instanceof TypeFunPtr) ) return GF; // Only fails during testing
        t = (TypeFunPtr)t.meet(td);
      }
      return t;
    }
    if( gvn._opt_mode == 2 ) {
      // See testUnresolvedAdd.
      // gcp - always a choice, as gcp starts highest and falls as required.
      // preserve choice until GCP resolves.
      // Post-GCP: never here unless in-error, or returning an ambiguous fun ptr

      // Ignores incoming types, as they are function pointers (code pointer
      // plus display) and goes straight to the FunNode._tf.
      TypeFunPtr t = GF;
      for( Node def : _defs ) {
        if( !(def instanceof FunPtrNode) ) return GF.dual(); // Only fails during testing
        TypeFunPtr tf = ((FunPtrNode)def).fun()._tf;
        tf = tf.dual();
        t = (TypeFunPtr)t.join(tf);
      }
      return t;
    }
    // Post-GCP.  Should be dead, except for primitive hooks.  If we inline,
    // we split a fidx and the Unresolved does not get both options... so it
    // runs "downhill" during iter.  Not useful, since dead.  Leave it set.
    return (TypeFunPtr)gvn.self_type(this);
  }

  // Filter out all the wrong-arg-count functions
  public Node filter( GVNGCM gvn, int nargs ) {
    Node x = null;
    for( Node epi : _defs ) {
      FunNode fun =  ((FunPtrNode)epi).fun();
      // User-nargs are user-visible #arguments.
      // Fun-nargs include the return and the display, hence the +2.
      if( fun.nargs() != nargs+2 ) continue;
      if( x == null ) x = epi;
      else if( x instanceof UnresolvedNode ) x.add_def(epi);
      else x = new UnresolvedNode(_bad,x,epi);
    }
    return x instanceof UnresolvedNode ? gvn.xform(x) : x;
  }

  // Compute local contribution of use liveness to this def.
  // If pre-GCP, same as value() above, use the conservative answer.
  // During GCP, this will resolve so use the optimistic answer.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( gvn._opt_mode < 2 ) return super.live_use(gvn,def);
    if( !(def instanceof FunPtrNode) ) return _live;
    // If any Call has resolved to this def, its alive.
    // If not a Call, must assume it props to some unknown Call and is alive.
    int dfidx = ((FunPtrNode)def).ret()._fidx;
    for( Node call : _uses )
      if( !(call instanceof CallNode) ||
          ((CallNode)call).live_use_call(gvn,dfidx) != TypeMem.DEAD )
        return _live;
    // Only call users, and no call wants this def.
    return TypeMem.DEAD;
  }

  @Override public TypeFunPtr all_type() { return TypeFunPtr.GENERIC_FUNPTR; }

  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte op_prec() {
    byte prec = _defs.at(0).op_prec();
    assert _defs._len < 2 || _defs.at(1).op_prec() == prec;
    return prec;
  }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte may_prec() {
    byte prec = -1;
    for( Node f : _defs ) if( (prec=f.op_prec()) >= 0 ) return prec;
    return prec;
  }
  @Override public int hashCode() { return super.hashCode()+(_bad==null ? 0 : _bad.hashCode()); }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _bad==((UnresolvedNode)o)._bad;
  }
  // Make a copy with an error message
  public UnresolvedNode copy(Parse bad) {
    return new UnresolvedNode(bad,Arrays.copyOf(_defs._es,_defs._len));
  }
  // True if unresolved is uncalled (but possibly returned or stored as a
  // constant).  Such code is not searched for errors.  Here we just check for
  // being ONLY used by the initial environment; if this value is loaded from,
  // it will have other uses.
  @Override boolean is_uncalled(GVNGCM gvn) {
    return _uses._len==0 || (_uses._len==1 && _uses.at(0)== Env.STK_0);
  }
  @Override public String err(GVNGCM gvn) {
    FunNode fun = ((FunPtrNode)in(0)).fun();
    String name = fun==null ? null : fun.xstr();
    return _bad==null ? null : _bad.errMsg("Unable to resolve "+name);
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
