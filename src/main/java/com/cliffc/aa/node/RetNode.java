package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class RetNode extends Node {
  final int _idx;               // 
  public RetNode( Node ctrl, Node ret, FunNode fun, int idx ) { super(ret); _idx=idx; }
  @Override String str() { return "ret"; }
  @Override public Node ideal(GVNGCP gvn) { throw AA.unimpl(); }
  @Override public Type value(GVNGCP gvn) { throw AA.unimpl(); }
  @Override public Type all_type() { return Type.SCALAR; }
}
