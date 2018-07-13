package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  private String _badgc;
  public PhiNode( String badgc, Node... vals) { super(OP_PHI,vals); _badgc = badgc; }
  PhiNode( byte op, Node fun, Node defalt, String badgc ) { super(op,fun,defalt); _badgc = badgc; } // For ParmNodes
  @Override public Node ideal(GVNGCM gvn) {
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( gvn.type(r) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    // TODO: can fold up all ANY control paths with ANY data; makes dead calcs
    // go dead sooner.
    return r._cidx == 0 ? null : in(r._cidx); // Region has collapsed to a Copy, fold up
  }
  @Override public Type value(GVNGCM gvn) {
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( r._cidx != 0 ) return gvn.type(in(r._cidx)); // Region has collapsed to a Copy, no need to run full merge
    Type t = TypeErr.ANY;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.in(i))!=Type.XCTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    if( t==Type.SCALAR )        // Cannot mix GC and non-GC types
      t = TypeErr.make(_badgc);
    return t;
  }
}
