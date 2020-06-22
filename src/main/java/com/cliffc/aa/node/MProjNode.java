package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj memory
public class MProjNode extends ProjNode {
  public MProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() { return "MProj_"+_idx; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    Node x = in(0).is_copy(gvn,_idx);
    if( x != null )
      return x == this ? gvn.con(TypeMem.XMEM) : x; // Happens in dead self-recursive functions
    if( in(0) instanceof CallEpiNode ) {
      Node precall = in(0).is_pure_call(); // See if memory can bypass pure calls (most primitives)
      if( precall != null && gvn.type(this)==gvn.type(precall) )
        return precall;
    }
    return null;
  }
  @Override public boolean basic_liveness() { return false; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return _live; }
}
