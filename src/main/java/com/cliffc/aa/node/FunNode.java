package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Function node; after construction will have one def pointing to the return
// results and all the ParmNodes will point to it.
public class FunNode extends Node {
  @Override String str() { return "{...}"; }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  @Override public Type value(GVNGCP gvn) { return Type.SCALAR; }
  @Override public Type all_type() { return Type.SCALAR; } // TODO: Function call any arg count
  @Override public void lift_type(Type t) { throw AA.unimpl(); }
}
