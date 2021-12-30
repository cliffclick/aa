package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

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
  }
  @Override public String xstr() {
    if( Env.ALL_PARM == this ) return "ALL_PARM";
    if( Env.ALL_CALL == this ) return "ALL_CALL";
    return _t==null ? "(null)" : _t.toString();
  }
  @Override public Type value() {
    return _t.simple_ptr();
  }
  @Override public TypeMem all_live() { return _t instanceof TypeMem ? TypeMem.ALLMEM : TypeMem.ALIVE; }

  @Override public TV2 new_tvar(String alloc_site) {
    if( _t==Type.CTRL || _t==Type.XCTRL || _t instanceof TypeRPC )
      return null;
    if( _t == Type.XNIL )
      return TV2.make_nil(TV2.make_leaf(this,alloc_site),alloc_site);
    return TV2.make_base(this,_t,alloc_site);
  }

  @Override public boolean unify( boolean test ) {
    if( _tvar==null ) return false;
    TV2 self = tvar();
    assert self.is_base() || self.is_nil() || self.is_obj();
    return false;
  }

  @Override public String toString() { return str(); }
  @Override public int hashCode() {
    // In theory also slot 0, but slot 0 is always Start.
    // Two XNILs are typically different because their TV2s are different
    return _t.hashCode();
  }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConNode con) ) return false;
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

