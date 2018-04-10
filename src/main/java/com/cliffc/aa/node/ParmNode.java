package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.SB;

// Function parameter node; just a pass-thru
public class ParmNode extends Node {
  final int _idx;               // Parameter index, 0-based
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
    if( _name.equals("$rpc") && TypeInt.con(1).isa(t) )
      return TypeInt.INT32;     // RPC-of-1 is the unknown call-site, cannot collapse until known-no-more-callsites
    return t;
  }
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
