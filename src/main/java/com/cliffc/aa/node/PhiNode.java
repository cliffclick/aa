package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final String _badgc;
  private final Type _default_type; //
  public PhiNode( String badgc, Node... vals) { super(OP_PHI,vals); _default_type = TypeErr.ALL; _badgc = badgc; }
  PhiNode( byte op, Node fun, ConNode defalt, String badgc ) { super(op,fun,defalt); _badgc = badgc; _default_type = defalt._t; } // For ParmNodes
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
    Type t = _default_type.dual();
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.in(i))!=Type.XCTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    return t;
  }
  @Override public Type all_type() { return _default_type; }
}
