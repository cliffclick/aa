package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.SB;

// Merge results
public class PhiNode extends Node {
  public PhiNode( Node... vals) { super(OP_PHI,vals); }
  @Override String str() { return "Phi"; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Node r = at(0);
    assert r instanceof RegionNode;
    assert r._defs._len==_defs._len;
    Type t = Type.XSCALAR;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.at(i))!=Type.ANY )
        t = t.meet(gvn.type(at(i)));
    return t;
  }
  @Override public Type all_type() { return Type.SCALAR; }
}
