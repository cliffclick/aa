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

    // If Store is by a New and no other Stores, trigger Store to fold into New
    if( _uses._len==1 && _uses.at(0) instanceof StoreNode )
      gvn.add_work(_uses.at(0));
    if( in(0) instanceof NewNode && ((NewNode)in(0))._captured )
      return gvn.con(TypeObj.XOBJ);
    
    return null;
  }
      
  // OProj lost a use; if down to 1 remaining use can fold up some back-to-back ops.
  @Override public boolean ideal_impacted_by_losing_uses(GVNGCM gvn, Node dead) { return _uses._len==1; }
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
