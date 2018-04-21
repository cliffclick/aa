package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Type;
import com.cliffc.aa.TypeErr;

// Merge results
public class RegionNode extends Node {
  public RegionNode( Node... ctrls) { super(OP_REGION,ctrls); }
  @Override String str() { return "Region"; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t = TypeErr.ANY;
    for( int i=1; i<_defs._len; i++ )
      t = t.meet(gvn.type(_defs._es[i]));
    return t;
  }
  @Override public Type all_type() { return Type.CONTROL; }
}
