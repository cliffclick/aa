package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Proj data
public class ProjNode extends Node {
  final int _idx;
  public ProjNode( Node ifn, int idx ) { super(OP_PROJ,ifn); _idx=idx; }
  @Override String str() { return "Proj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn) {
    // If a CallNode 
    Node m = at(0);
    if( m instanceof TypeNode ) {
      TypeNode t = (TypeNode)m;
      assert m.at(1) instanceof CallNode;
      assert _idx==0 || _idx==1;
      if( _idx==0 ) { set_def(0,m.at(1),gvn); return this; }
      else return new TypeNode(((TypeTuple)t._t).at(1),gvn.xform(new ProjNode(m.at(1),1)),t._msg);
    }
    return m.is_copy(gvn,_idx);
  }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(at(0));
    if( c instanceof TypeErr ) return c; // Handle error input
    if( !(c instanceof TypeTuple) )
      throw AA.unimpl();
    return ((TypeTuple)c).at(_idx); // Otherwise our type is just the matching tuple slice
  }

  @Override public Type all_type() { return Type.SCALAR; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ProjNode) ) return false;
    ProjNode proj = (ProjNode)o;
    return _idx==proj._idx;
  }
}
