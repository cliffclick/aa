package com.cliffc.aa.node;

import com.cliffc.aa.*;

public final class ConNode<T extends Type> extends Node {
  T _t;
  public ConNode( T t ) { super(Env.ROOT); _t=t; }
  @Override String str() { return _t.toString(); }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  @Override public Type value(GVNGCP gvn) { return _t; }
  @Override public Type all_type() { return _t; }
  @Override public String toString() { return str(); }
  @Override public int hashCode() { return _t.hashCode(); }// In theory also slot 0, but slot 0 is always Root
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConNode) ) return false;
    ConNode con = (ConNode)o;
    return _t==con._t;
  }
}

