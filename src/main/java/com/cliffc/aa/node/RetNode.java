package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Jump-to a specific RPC
public class RetNode extends Node {
  final int _rpc;
  public RetNode( Node epi, int rpc ) { super(OP_RET,epi); _rpc=rpc; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    // If the epi includes this RPC or not
    throw AA.unimpl();
  }
}
