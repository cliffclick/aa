package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

import java.util.function.Predicate;

// Program execution start
public class StartNode extends Node {
  public StartNode() { super(OP_START); }
  @Override public Type value(GVNGCM.Mode opt_mode) { return TypeTuple.START_STATE; }
  // StartNodes are never equal
  @Override public int hashCode() { return 123456789+1; }
  @Override public boolean equals(Object o) { return this==o; }
  // TODO: Since new constants can appear at any time, we must assume as bad as
  // a new constant.  A better answer is to make new constants appear with the
  // same liveness as their users.
  @Override public TypeMem live(GVNGCM.Mode opt_mode) { return TypeMem.ESCAPE; }
  @Override Node walk_dom_last( Predicate<Node> P) { return null; }
}
