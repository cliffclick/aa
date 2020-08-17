package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Program memory start
public class StartMemNode extends Node {
  public StartMemNode(StartNode st) { super(OP_STMEM,st); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(byte opt_mode) {
    // All things are '~use' (to-be-allocated)
    return TypeMem.ANYMEM;
  }
  @Override public boolean basic_liveness() { return false; }
  // StartMemNodes are never equal
  @Override public int hashCode() { return 123456789+2; }
  @Override public boolean equals(Object o) { return this==o; }
}
