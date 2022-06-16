package com.cliffc.aa.node;

import com.cliffc.aa.Env;
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
    super(OP_CON,Env.ROOT);
    assert t.simple_ptr()==t;
    _t=t;
  }
  @Override public String xstr() {
    return _t==null ? "(null)" : _t.toString();
  }

  @SuppressWarnings("unchecked")
  public void set_alias(int alias,TypeStruct ts) {
    unelock();                  // Changing hash
    _t = (T)((TypeMem)_t).make_from(alias,ts);
    Env.GVN.add_flow(this);
  }

  @Override public Type value() { return _t; }

  @Override public boolean has_tvar() {
    if( _t.is_simple() ) return false; // No on CTRL, XCTRL, ANY, ALL
    if( _t instanceof TypeRPC ) return false; // For now, no closures
    if( _t.is_nil() ) return true;     // Yes on NIL, INT, FLT, MEMPTR, FUNPTR
    if( _t instanceof TypeStruct ) return true;
    if( _t instanceof TypeAry ) throw unimpl(); // Probably yes, undecided
    // No for TFLD, TMEM
    return false;
  }

  @Override TV2 new_tvar() {
    return _t==TypeNil.XNIL
      ? TV2.make_nil(TV2.make_leaf("ConNode_notnil"),"ConNode_nilable")
      : TV2.make(_t, "ConNode_base");
  }
  
  @Override public boolean unify( boolean test ) {
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
    if( _t==TypeNil.NIL && con._t==TypeNil.NIL )
      return false;             // Different versions of TV2 NotNil
    return _t==con._t;
  }
  @Override Node walk_dom_last( Predicate<Node> P) { return null; }
  @SuppressWarnings({"unused","unchecked"}) // Found as java_class_node in _prims.aa
  public static class PI extends ConNode {
    public PI() { super(TypeFlt.PI); }
    @Override public Node clazz_node( ) { return Env.GVN.init(this); }
  }
}

