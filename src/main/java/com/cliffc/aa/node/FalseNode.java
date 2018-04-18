package com.cliffc.aa.node;

import com.cliffc.aa.*;

// False control.
public class FalseNode extends Node {
  public FalseNode( Node ifn ) { super(OP_FALSE,ifn); }
  @Override String str() { return "False"; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    return Type.CONTROL;
  }
  @Override public Type all_type() { return Type.CONTROL; }
}
