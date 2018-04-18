package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.SB;

// Merge results
public class PhiNode extends Node {
  public PhiNode( Node... vals) { super(OP_PHI,vals); }
  @Override String str() { return "Phi"; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    // TODO: only meet known-live incoming call-paths
    Type t = Type.XSCALAR;
    for( int i=1; i<_defs._len; i++ )
      t = t.meet(gvn.type(_defs._es[i]));
    return t;
  }
  @Override public Type all_type() { return Type.SCALAR; }
}
