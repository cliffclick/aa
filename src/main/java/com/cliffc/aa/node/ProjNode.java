package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;
import com.cliffc.aa.type.TypeTuple;

// Proj data
public class ProjNode extends Node {
  final int _idx;
  public ProjNode( Node ifn, int idx ) { super(OP_PROJ,ifn); _idx=idx; }
  @Override String xstr() { return "DProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn) {
    Node m = in(0);
    if( m instanceof CallNode ) {
      // If a CallNode with an upcast on the data return?
      CallNode call = (CallNode)m;
      TypeNode callcast = call.upcast_return(gvn);
      if( callcast != null )
        return callcast.set_def(1,gvn.init(new ProjNode(call,_idx)),gvn);
    }
    return m.is_copy(gvn,_idx);
  }
  @Override public Type value_ne(GVNGCM gvn) {
    Type c = gvn.type_ne(in(0));
    return ((TypeTuple)c).at(_idx); // Otherwise our type is just the matching tuple slice
  }

  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ProjNode) ) return false;
    ProjNode proj = (ProjNode)o;
    return _idx==proj._idx;
  }
}
