package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj memory
public class MProjNode extends ProjNode {
  public MProjNode( CallNode call, DefMemNode def ) { super(AA.MEM_IDX,call,def); }
  public MProjNode( Node head ) { super(head, AA.MEM_IDX); }
  public MProjNode( Node head, int idx ) { super(head,idx); }
  @Override public String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }
  
  @Override public Node ideal(GVNGCM gvn, int level) { throw com.cliffc.aa.AA.unimpl(); }
  @Override public Node ideal_reduce() {
    Node x = super.ideal_reduce();
    if( x!=null ) return x;
    if( in(0) instanceof CallEpiNode ) {
      Node precall = in(0).is_pure_call(); // See if memory can bypass pure calls (most primitives)
      if( precall != null && val() == precall.val() )
        return precall;
    }
    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type c = val(0);
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length ) {
        Type t = ct.at(_idx);
        // Break forward dead-alias cycles in recursive functions by inspecting
        // dead-ness in DefMem.
        if( in(0) instanceof CallNode )
          t = t.join(in(1).val());
        return t;
      }
    }
    return c.oob();
  }


  @Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return _live; }
}
