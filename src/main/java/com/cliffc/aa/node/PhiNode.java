package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  public PhiNode( Node... vals) { super(OP_PHI,vals); }
  PhiNode( byte op, Node fun, Node defalt ) { super(op,fun,defalt); } // For ParmNodes
  @Override public Node ideal(GVNGCM gvn) {
    RegionNode r = (RegionNode)at(0);
    assert r._defs._len==_defs._len;
    if( gvn.type(r) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    // TODO: can fold up all ANY control paths with ANY data; makes dead calcs
    // go dead sooner.
    return r._cidx == 0 ? null : at(r._cidx); // Region has collapsed to a Copy, fold up
  }
  @Override public Type value(GVNGCM gvn) {
    RegionNode r = (RegionNode)at(0);
    assert r._defs._len==_defs._len;
    if( r._cidx != 0 ) return gvn.type(at(r._cidx)); // Region has collapsed to a Copy, no need to run full merge
    Type t = Type.XSCALAR;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.at(i))!=Type.XCTRL ) // Only meet alive paths
        t = t.meet(gvn.type(at(i)));
    return t;
  }
}
