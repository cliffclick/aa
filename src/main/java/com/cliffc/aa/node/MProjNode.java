package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

// Proj memory
public class MProjNode extends ProjNode {
  public MProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() {
    return "MProj_"+_idx;
  }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    return TypeMem.MEM;
  }
  @Override public Type all_type() { return TypeMem.MEM; }
}
