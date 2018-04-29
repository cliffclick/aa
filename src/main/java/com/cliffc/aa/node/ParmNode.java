package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  final int _idx;               // Parameter index, 1-based
  final String _name;           // Parameter name
  public ParmNode( int idx, String name, Node fun, Node defalt) { super(OP_PARM,fun,defalt); _idx=idx; _name=name; }
  @Override String str() { return _name; }
  @Override public Type all_type() { return Type.SCALAR; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode) ) return false;
    ParmNode parm = (ParmNode)o;
    return _idx==parm._idx;
  }
}
