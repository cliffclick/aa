package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj memory
public class MProjNode extends ProjNode {
  public MProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() { return "MProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    Node x = in(0).is_copy(gvn,_idx);
    if( x == null ) return null;
    if( x != this ) return x;
    return gvn.con(TypeMem.XMEM);// Happens in dead self-recursive functions
  }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(in(0));
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length )
        return ct._ts[_idx];
    }
    return c.above_center() ? TypeMem.XMEM : TypeMem.MEM;
  }
  // Memory need precise liveness
  @Override public boolean basic_liveness() { return false; }
  @Override public Type all_type() { return TypeMem.MEM; }
}
