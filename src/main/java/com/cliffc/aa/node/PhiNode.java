package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final String _badgc;
  public PhiNode( String badgc, Node... vals ) {
    super(OP_PHI,vals);
    _badgc = badgc;
  }
  PhiNode( byte op, Node fun, ConNode defalt, String badgc ) { super(op,fun,defalt); _badgc = badgc; } // For ParmNodes
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
    Type ctl = gvn.type(in(0));
    if( ctl != Type.CTRL ) return ctl.above_center() ? Type.ANY : Type.ALL;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.in(i))==Type.CTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    return t;                   // Limit to sane results
  }
  @Override public Type all_type() { return Type.ALL; }
}
