package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Sea-of-Nodes
public class RootNode extends Node {
  public RootNode() { super(OP_ROOT); }
  @Override String str() { return "root"; }
  @Override public String toString() { return "root"; } // TOoOoOo many use/defs, print none
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return Type.ALL; }
  // RootNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  @Override public int hashCode() { return 123456789; }
}
