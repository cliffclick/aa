package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj object
public class OProjNode extends ProjNode {
  public OProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() { return "OProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    Node n = in(0).is_copy(gvn,_idx);
    if( n != null ) return n;

    Type t = captured();
    if( t != null ) return gvn.con(t);
    
    return null;
  }
      
  @Override public Type value(GVNGCM gvn) {
    Type t = captured();
    if( t != null ) return t;
    Type c = gvn.type(in(0));
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length )
        return ct._ts[_idx];
    }
    return c.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
  }
  // Return not-null if NewNode is captured and being removed.  This alias goes
  // dead.
  private TypeObj captured() {
    if( in(0) instanceof NewNode && ((NewNode)in(0))._captured )
      return in(0) instanceof NewObjNode ? TypeStruct.ANYSTRUCT : TypeObj.XOBJ;
    return null;
  }
  // Object needs precise liveness
  @Override public boolean basic_liveness() { return false; }
  @Override public Type all_type() { return ((TypeTuple)in(0).all_type())._ts[_idx]; }
}
