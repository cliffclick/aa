package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV2;

import java.util.function.Predicate;

// Constant value nodes; no computation needed.  Hashconsed for unique
// constants, except for XNIL.  XNIL allows for a TV2 typevar Nilable-Leaf with
// each Leaf unifying on its own.
public class ConNode<T extends Type> extends Node {
  T _t;                         // Not final for testing
  public ConNode( T t ) {
    super(OP_CON,Env.START);
    _t=t;
    _live = all_live();
    if( t==Type.CTRL || t==Type.XCTRL || t instanceof TypeRPC )
      { _tvar.free(); _tvar=null; }
  }
  // Allows ANY type with a normal unification, used for uninitialized variables
  // (as opposed to dead ones).
  public ConNode( T t, double dummy ) {
    super(OP_CON,Env.START);
    _t=t;
  }
  // Used by FunPtrNode
  ConNode( byte type, T tfp, RetNode ret, Node closure ) { super(type,ret,closure); _t = tfp; }
  @Override public String xstr() { return Env.ALL_CTRL == this ? "ALL_CTL" : (_t==null?"(null)":_t.toString()); }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    // ALL_CTRL is used for unknown callers; during and after GCP there are no
    // unknown callers.  However, we keep the ALL_CTRL for primitives, so we can
    // reset the compilation state easily.
    if( opt_mode._CG && Env.ALL_CTRL == this ) return Type.XCTRL;
    return _t.simple_ptr();
  }
  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // If any use is alive, the Con is alive... but it never demands memory.
    // Indeed, it may supply memory.
    if( _keep>0 ) return all_live();
    TypeLive live = TypeLive.DEAD; // Start at lattice top
    for( Node use : _uses )
      if( use.live_uses() )
        live = live.lmeet(use.live_use(opt_mode,this).live());
    return TypeMem.make_live(live);
  }
  @Override public TypeMem all_live() { return _t==Type.CTRL ? TypeMem.ALIVE : (_t instanceof TypeMem ? TypeMem.ALIVE : TypeMem.LIVE_BOT); }

  @Override public boolean unify( Work work ) {
    TV2 self = tvar();
    if( self.is_base() || self.is_nilable() || self.is_struct() || self.isa("Str") ) return false;
    if( work==null ) return true;
    assert self.is_leaf();
    String asite = "Con_unify";
    TV2 tv2 = _t==Type.XNIL ? TV2.make_nil(this,_t,TV2.make_leaf(this,asite),asite) : TV2.make_base(this,_t,asite);
    return self.unify(tv2,work);
  }

  @Override public String toString() { return str(); }
  @Override public int hashCode() { return _t.hashCode(); }// In theory also slot 0, but slot 0 is always Start
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConNode) ) return false;
    ConNode con = (ConNode)o;
    return _t!=Type.XNIL && _t==con._t;
  }
  @Override Node walk_dom_last( Predicate<Node> P) { return null; }
}

