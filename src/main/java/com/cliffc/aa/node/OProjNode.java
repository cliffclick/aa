package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj object
public class OProjNode extends ProjNode {
  public OProjNode( Node ifn, int idx ) { super(idx, ifn); }
  @Override String xstr() { return "OProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // Only memory use is default memory - means no loads, no stores.  Only the
    // pointer-use remains.
    if( _uses._len==1 ) {
      assert _uses.at(0)==Env.DEFMEM;
      return gvn.con(TypeObj.UNUSED);
    }
    return null;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type c = val(0);
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length )
        return ct._ts[_idx];
    }
    return c.oob(TypeObj.OBJ);
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return _live; }
  int alias() { return ((NewNode)in(0))._alias; }
}
