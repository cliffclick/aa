package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV2;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MProjNode extends ProjNode {

  public MProjNode( CallNode call, Node def ) { super(MEM_IDX,call,def); }
  public MProjNode( Node head ) { super(head, MEM_IDX); }
  public MProjNode( Node head, int idx ) { super(head,idx); }
  @Override public String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }

  @Override public Node ideal_reduce() {
    Node x = super.ideal_reduce();
    if( x!=null ) return x;
    if( in(0) instanceof CallEpiNode ) {
      Node precall = in(0).is_pure_call(); // See if memory can bypass pure calls (most primitives)
      if( precall != null && _val == precall._val )
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
        if( in(0) instanceof CallNode && !opt_mode._CG)
          t = t.join(in(1)._val);
        return t;
      }
    }
    return c.oob();
  }

  @Override public TV2 new_tvar( String alloc_site) { return TV2.make_mem(this,alloc_site); }

  @Override public void add_flow_use_extra(Node chg) {
    if( chg instanceof CallNode ) { // If the Call changes value
      Env.GVN.add_flow(chg.in(MEM_IDX));       // The called memory   changes liveness
      Env.GVN.add_flow(((CallNode)chg).fdx()); // The called function changes liveness
    }
  }

  @Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return opt_mode._CG && def==Env.DEFMEM ? TypeMem.DEAD : _live;
  }
}
