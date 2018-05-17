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
  @Override public Node ideal(GVNGCM gvn) { return at(0).is_copy(gvn,_idx); }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(at(0));
    if( c==TypeErr.ANY ) return TypeErr.ANY; // Handle totally dead input
    if( !(c instanceof TypeTuple) )
      throw AA.unimpl();
    return ((TypeTuple)c).at(_idx); // Otherwise our type is just the matching tuple slice
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
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }
}
