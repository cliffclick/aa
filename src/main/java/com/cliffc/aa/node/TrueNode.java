package com.cliffc.aa.node;

import com.cliffc.aa.*;

// True control
public class TrueNode extends Node {
  public TrueNode( Node ifn ) { super(OP_TRUE,ifn); }
  @Override String str() { return "True"; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    return Type.CONTROL;
  }
  @Override public Type all_type() { return Type.CONTROL; }
}
