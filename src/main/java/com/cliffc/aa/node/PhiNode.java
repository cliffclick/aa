package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Type;

// Merge results
public class PhiNode extends Node {
  public PhiNode( Node... vals) { super(OP_PHI,vals); }
  @Override String str() { return "Phi"; }
  @Override public Node ideal(GVNGCM gvn) {
    Node r = at(0);
    assert r instanceof RegionNode;
    assert r._defs._len==_defs._len;
    if( gvn.type(r) == Type.ANY ) return null; // All dead, c-prop will fold up
    // If only 1 input path is alive, we become an identity on that path
    int idx = -1;               // Index of the one alive path
    for( int i=1; i<r._defs._len; i++ )
      if( gvn.type(r.at(i))!=Type.ANY ) // Found a live path
        if( idx == -1 ) idx = i;        // Remember live path
        else return null;               // Some other output is alive also
    return idx== -1 ? null : at(idx);   // Return the 1 alive path
  }
  @Override public Type value(GVNGCM gvn) {
    Node r = at(0);
    assert r instanceof RegionNode;
    assert r._defs._len==_defs._len;
    Type t = Type.XSCALAR;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.at(i))!=Type.ANY ) // Only meet alive paths
        t = t.meet(gvn.type(at(i)));
    return t;
  }
}
