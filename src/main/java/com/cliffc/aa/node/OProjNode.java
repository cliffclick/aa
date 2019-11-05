package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj object
public class OProjNode extends ProjNode {
  public OProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() { return "OProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn) { return in(0).is_copy(gvn,_idx); }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(in(0));
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length )
        return ct._ts[_idx];
    }
    return c.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
  }
  @Override public Type all_type() { return TypeObj.OBJ; }
  // Split this node into a set returning 'bits' and the original which now
  // excludes 'bits'.  Return null if already making a subset of 'bits'.
  Node split_memory_use( GVNGCM gvn, BitsAlias bits ) { return null; } // Happens when next to a New
}
