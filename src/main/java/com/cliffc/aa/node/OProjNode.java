package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj object
public class OProjNode extends ProjNode {
  public OProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() { return "OProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn) { return in(0).is_copy(gvn,_idx); }
  @Override public Type value(GVNGCM gvn) {
    if( in(0) instanceof NewNode && ((NewNode)in(0))._captured )
      return TypeObj.XOBJ;
    Type c = gvn.type(in(0));
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length )
        return ct._ts[_idx];
    }
    return c.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
  }
  @Override public Type all_type() { return TypeObj.OBJ; }
}
