package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

import java.util.function.Predicate;

// Program execution start
public class StartNode extends Node {
  public StartNode() { super(OP_START); }
  @Override public Type value() { return TypeTuple.START_STATE; }
  @Override public Type live() { return Type.ALL; }
  //@Override public TV2 new_tvar(String alloc_site) { return TV2.make("Start",this,alloc_site); }
  // StartNodes are never equal
  @Override public int hashCode() { return 123456789+1; }
  @Override public boolean equals(Object o) { return this==o; }
  @Override Node walk_dom_last( Predicate<Node> P) { return null; }
  @Override public TV2 new_tvar(String alloc_site) { return TV2.make_leaf(this,alloc_site); }
}
