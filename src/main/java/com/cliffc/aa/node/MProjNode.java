package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj memory
public class MProjNode extends ProjNode {
  public MProjNode( Node ifn, int idx ) { super(idx, ifn); }
  @Override String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    Node x = in(0).is_copy(gvn,_idx);
    if( x != null )
      return x == this ? gvn.con(TypeMem.ANYMEM) : x; // Happens in dead self-recursive functions
    if( in(0) instanceof CallEpiNode ) {
      Node precall = in(0).is_pure_call(); // See if memory can bypass pure calls (most primitives)
      if( precall != null && _val==precall._val )
        return precall;
    }
    return null;
  }
  @Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return _live; }
}
