package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  public final String _badgc;
  final Type _default_type;
  public PhiNode( String badgc, Node... vals) { super(OP_PHI,vals); _default_type = Type.SCALAR; _badgc = badgc; }
  PhiNode( byte op, Node fun, ConNode defalt, String badgc ) { super(op,fun,defalt); _badgc = badgc; _default_type = defalt._t; } // For ParmNodes
  @Override public Node ideal(GVNGCM gvn) {
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( gvn.type(r) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    return r._defs.len() == 2 ? in(1) : null; // Region has collapsed to a Copy, fold up
  }
  @Override public Type value(GVNGCM gvn) {
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    Type t = _default_type.dual();
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.in(i))!=Type.XCTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    return t;
  }
  @Override public Type all_type() { return _default_type; }
}
