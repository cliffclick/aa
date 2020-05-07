package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj object
public class OProjNode extends ProjNode {
  public OProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() { return "OProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // Only memory use is default memory - means no loads, no stores.  Only the
    // pointer-use remains.
    if( _uses._len==1 ) {
      assert _uses.at(0)==Env.DEFMEM;
      return gvn.con(TypeObj.UNUSED);
    }
    if( DefMemNode.CAPTURED.get(alias()) )
      return gvn.con(TypeObj.UNUSED);
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(in(0));
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length )
        return ct._ts[_idx];
    }
    return c.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
  }
  int alias() { return ((NewNode)in(0))._alias; }
  // Object needs precise liveness
  @Override public boolean basic_liveness() { return false; }
  @Override public Type all_type() { return ((TypeTuple)in(0).all_type())._ts[_idx]; }
}
