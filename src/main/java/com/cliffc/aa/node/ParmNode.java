package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.SB;

// Function parameter node; just a pass-thru
public class ParmNode extends Node {
  final int _idx;               // Parameter index, 1-based
  final String _name;           // Parameter name
  public ParmNode( int idx, String name, Node... funparms) { super(OP_PARM,funparms); _idx=idx; _name=name; }
  @Override String str() { return _name; }
  @Override public String toString() {
    SB sb = new SB().p(_name).p('{');
    boolean first = true;
    for( Node n : _defs ) { sb.p(first?"_":n.str()).p(' '); first=false; }
    return sb.p('}').toString();
  }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  @Override public Type value(GVNGCP gvn) {
    Type t = Type.XSCALAR;
    for( int i=1; i<_defs._len; i++ )
      t = t.meet(gvn.type(_defs._es[i]));
    return t;
  }
  @Override public Type all_type() { return Type.SCALAR; }
}
