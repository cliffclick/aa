package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;

public final class ConNode<T extends Type> extends Node {
  T _t;
  public ConNode( T t ) { super(OP_CON,Env.top_scope()); _t=t; }
  @Override String xstr() { return _t.toString(); }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value_ne(GVNGCM gvn) { return _t; }
  @Override public Type all_type() {
    if( _t==_t.dual() ) return _t;
    if( _t.isa(_t.dual()) ) return _t.dual();
    assert _t.dual().isa(_t);
    return _t;
  }
  @Override public String toString() { return str(); }
  @Override public int hashCode() { return _t.hashCode(); }// In theory also slot 0, but slot 0 is always Root
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConNode) ) return false;
    ConNode con = (ConNode)o;
    return _t==con._t;
  }
  @Override public byte op_prec() { return _t.op_prec(); }
  
}

