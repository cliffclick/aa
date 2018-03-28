package com.cliffc.aa.node;

import com.cliffc.aa.*;

public class ConNode<T extends Type> extends Node {
  T _t;
  public ConNode( T t ) { _t=t; }
  @Override String str() { return _t.toString(); }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  @Override public Type value(GVNGCP gvn) { return _t; }
  @Override public Type all_type() { return _t; }
  @Override public void lift_type(Type t) { _t=(T)t; }
  @Override public String toString() { return str(); }
}

