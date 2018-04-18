package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); }
  @Override String str() { return "If"; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    return TypeTuple.IF_CTRL;
  }
  @Override public Type all_type() { return TypeTuple.IF_CTRL; }
}
