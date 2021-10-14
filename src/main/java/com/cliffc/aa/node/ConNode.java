package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;

// Constant value nodes; no computation needed.  Hashconsed for unique
// constants, except for XNIL.  XNIL allows for a TV2 typevar Nilable-Leaf with
// each Leaf unifying on its own.
public class ConNode<T extends Type> extends Node {
  T _t;                         // Not final for testing
  public ConNode( T t ) {
    super(OP_CON,Env.START);
    _t=t;
    _live = all_live();
  }
  // Allows ANY type with a normal unification, used for uninitialized variables
  // (as opposed to dead ones).
  public ConNode( T t, double dummy ) {
    super(OP_CON,Env.START);
    _t=t;
  }
  // Used by FunPtrNode
  ConNode( byte type, T tfp, RetNode ret, Node closure ) { super(type,ret,closure); _t = tfp; }
  @Override public String xstr() {
    if( Env.ALL_PARM == this ) return "ALL_PARM";
    if( Env.ALL_CALL == this ) return "ALL_CALL";
    return _t==null ? "(null)" : _t.toString();
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
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

  @Override public TV2 new_tvar(String alloc_site) {
    if( _t==Type.CTRL || _t==Type.XCTRL || _t instanceof TypeRPC )
      return null;
    if( _t == Type.XNIL )
      return TV2.make_nil(TV2.make_leaf(this,alloc_site),alloc_site);
    return TV2.make_base(this,_t,alloc_site);
  }

  @Override public boolean unify( Work work ) {
    if( _tvar==null ) return false;
    TV2 self = tvar();
    if( self.is_base() || self.is_nil() || self.is_struct() || self.isa("Str") ) return false;
    if( work==null ) return true;
    //assert self.is_leaf();
    //_set_tvar();
    //return true;
    throw unimpl();
  }

  @Override public String toString() { return str(); }
  @Override public int hashCode() {
    // In theory also slot 0, but slot 0 is always Start.
    // Two XNILs are typically different because their TV2s are different
    return _t.hashCode();
  }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConNode) ) return false;
    ConNode con = (ConNode)o;
    if( this== Env.ALL_PARM || con == Env.ALL_PARM ) return false; // Only equal to itself
    if( this== Env.ALL_CALL || con == Env.ALL_CALL ) return false; // Only equal to itself
    if( _t==Type.XNIL && con._t==Type.XNIL /*&& tvar()!=con.tvar()*/ )
      return false;             // Different versions of TV2 NotNil
    return _t==con._t;
  }
  @Override Node walk_dom_last( Predicate<Node> P) { return null; }
  @SuppressWarnings("unchecked")
  public static class PI extends ConNode {
    public PI() { super(TypeFlt.PI); }
    @Override public Node clazz_node( ) { return this; }
  }
}

