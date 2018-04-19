package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Proj control
public class ProjNode extends Node {
  final int _idx;
  public ProjNode( Node ifn, int idx ) { super(OP_PROJ,ifn); _idx=idx; }
  @Override String str() {
    if( at(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "Proj_"+_idx;
  }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(at(0));
    if( c==Type.ANY ) return Type.ANY;
    if( !(c instanceof TypeTuple) )
      throw AA.unimpl();
    TypeTuple cs = (TypeTuple)c;
    return cs._ts[_idx];
  }
  @Override public Type all_type() { return Type.CONTROL; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ProjNode) ) return false;
    ProjNode proj = (ProjNode)o;
    return _idx==proj._idx;
  }
}
