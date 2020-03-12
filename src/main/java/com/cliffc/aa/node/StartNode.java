package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;

// Program execution start
public class StartNode extends Node {
  public StartNode() { super(OP_START); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) { return all_type(); }
  // TmStartNodes are never equal
  @Override public int hashCode() { return 123456789+1; }
  @Override public boolean equals(Object o) { return this==o; }
  @Override public Type all_type() { return TypeTuple.START_STATE; }
}
