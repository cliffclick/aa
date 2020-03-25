package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

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
  @Override public Type value(GVNGCM gvn) {
    if( gvn._opt_mode < 2 ) { // parse or 1st iter: assume all can happen, and hope to resolve to lift
      Type t = TypeFunPtr.GENERIC_FUNPTR.dual();
      for( Node def : _defs )
        t = t.meet(gvn.type(def));
      return t;
    } else if( gvn._opt_mode == 2 ) {
      // gcp - always a choice, as gcp starts highest and falls as required.
      // preserve choice until GCP resolves.
      // Post-GCP: never here unless in-error, or returning an ambiguous fun ptr

      // Unresolved is a *choice* and thus a *join* until resolved.
      Type t = TypeFunPtr.GENERIC_FUNPTR;
      for( Node def : _defs ) {
        Type tf = gvn.type(def);
        if( tf instanceof TypeFunPtr )
          tf = ((TypeFunPtr)tf).make_high_fidx();
        t = t.join(tf);
      }
      return t;
    } else {
      // Post-GCP.  Should be dead, except for primitive hooks.  If we inline,
      // we split a fidx and the Unresolved does not get both options... so it
      // runs "downhill" during iter.  Not useful, since dead.  Leave it set.
      return gvn.self_type(this);
    }
  }
  // Filter out all the wrong-arg-count functions
  public Node filter( GVNGCM gvn, int nargs ) {
    Node x = null;
    for( Node epi : _defs ) {
      FunNode fun =  ((FunPtrNode)epi).fun();
      if( fun.nargs() != nargs+1 ) continue;
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
    int dfidx = ((FunPtrNode)def).ret()._fidx;
    for( Node call : _uses )
      if( call instanceof CallNode ) {
        Type tfx = ((TypeTuple)gvn.type(call)).at(2);
        if( tfx instanceof TypeFunPtr &&
            ((TypeFunPtr)tfx).fidxs().abit() == dfidx )
          return _live;
      }
    // No call wants this def
    return TypeMem.DEAD;
  }
  // Too preserve the sharp display pointer types, this has to be as sharp as
  // the meet of its all_type inputs.  This can be cached locally here after
  // inputs stop changing... which is really just after we initialize all the
  // primitives.  Simpler to just recompute, which doesn't happen very often.
  @Override public TypeFunPtr all_type() {
    Type t = TypeFunPtr.GENERIC_FUNPTR.dual();
    for( Node def : _defs )
      t = t.meet(((FunPtrNode)def)._t);
    return (TypeFunPtr)t;
  }

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
    String name = ((FunPtrNode)in(0)).fun().xstr();
    return _bad==null ? null : _bad.errMsg("Unable to resolve "+name);
  }
}
