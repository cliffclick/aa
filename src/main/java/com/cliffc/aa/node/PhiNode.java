package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final String _badgc;
  Type _default_type;
  public PhiNode( String badgc, Node... vals) { this(badgc,Type.SCALAR,vals); }
  public PhiNode( String badgc, Type defalt, Node... vals) { super(OP_PHI,vals); _default_type = defalt; _badgc = badgc; }
  PhiNode( byte op, Node fun, ConNode defalt, String badgc ) { super(op,fun,defalt); _badgc = badgc; _default_type = defalt._t; } // For ParmNodes
  @Override public Node ideal(GVNGCM gvn) {
    if( gvn.type(in(0)) == Type.XCTRL ) return null;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( gvn.type(r) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    if( r._defs.len() > 1 &&  r.in(1) == Env.ALL_CTRL ) return null;
    // If only 1 unique live input, return that
    Node live=null;
    for( int i=1; i<_defs._len; i++ ) {
      if( gvn.type(r.in(i))==Type.XCTRL ) continue; // Ignore dead path
      if( in(i)==this || in(i)==live ) continue;    // Ignore self or duplicates
      if( live==null ) live = in(i);                // Found unique live input
      else return null;         // Found 2nd live input, no collapse
    }
    return live;                // Single unique input
  }
  @Override public Type value(GVNGCM gvn) {
    Type t = _default_type.dual();
    if( gvn.type(in(0)) == Type.XCTRL ) return t;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.in(i))!=Type.XCTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    return t.bound(_default_type);
  }
  @Override public Type all_type() { return _default_type; }
}
