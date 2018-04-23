package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class CastNode extends Node {
  final Type _t;                // TypeVar???
  public CastNode( Node ctrl, Type t ) { super(OP_CAST,ctrl); _t=t; }
  @Override String str() { return "("+_t+")"; }
  @Override public Node ideal(GVNGCM gvn) {
    // Can eliminate if the cast is useless
    throw AA.unimpl();
  }
  @Override public Type value(GVNGCM gvn) {
    // Upcast result
    throw AA.unimpl();
  }
  @Override public Type all_type() { return Type.SCALAR; }
}
