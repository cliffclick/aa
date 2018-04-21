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
  @Override public Node ideal(GVNGCM gvn) {
    // If this value is ANY, then this is dead and becomes an ANY
    if( value(gvn)==TypeErr.ANY ) return gvn.con(TypeErr.ANY);
    // If the control type is a tuple with a single CONTROL and we are that
    // CONTROL - we become the CONTROL's CONTROL.
    Type c = gvn.type(at(0));
    if( !(c instanceof TypeTuple) )
      throw AA.unimpl();
    TypeTuple cs = (TypeTuple)c;
    for( int i=0; i<cs._ts.length; i++ )
      if( i!=_idx && cs._ts[i]!=TypeErr.ANY ) // Some output (other than this) alive?
        return null;            // Some other output is alive also
    return at(0).at(0);         // We become the dominate control, and the parent test is dead
  }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(at(0));
    if( c==TypeErr.ANY ) return TypeErr.ANY; // Handle totally dead input
    if( !(c instanceof TypeTuple) )
      throw AA.unimpl();
    TypeTuple cs = (TypeTuple)c;
    return cs._ts[_idx]; // Otherwise our type is just the matching tuple slice
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
