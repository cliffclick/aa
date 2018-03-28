package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Function parameter node; just a pass-thru
public class ParmNode extends Node {
  final int _idx;               // Parameter index, 1-based
  final String _name;           // Parameter name
  public ParmNode( FunNode fun, int idx, String name ) { super(fun); _idx=idx; _name=name; }
  @Override String str() { return _name; }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  @Override public Type value(GVNGCP gvn) { return Type.SCALAR; }
  @Override public Type all_type() { return Type.SCALAR; }
  @Override public void lift_type(Type t) { throw AA.unimpl(); }
}
