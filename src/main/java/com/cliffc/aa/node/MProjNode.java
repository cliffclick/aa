package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MProjNode extends ProjNode {

  public MProjNode( Node head ) { super(head, MEM_IDX); }
  public MProjNode( Node head, int idx ) { super(head,idx); }
  @Override public String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }

  @Override public Node ideal_reduce() {
    Node x = super.ideal_reduce();
    if( x!=null ) return x;
    // TODO: Turn back on, as a local flow property
    //if( in(0) instanceof CallEpiNode ) {
    //  Node precall = in(0).is_pure_call(); // See if memory can bypass pure calls (most primitives)
    //  if( precall != null && _val == precall._val )
    //    return precall;
    //}
    return null;
  }

  @Override public Type value() {
    Type c = val(0);
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length )
        return ct.at(_idx);
    }
    return c.oob();
  }

  @Override public TV2 new_tvar( String alloc_site) { return null; }

  @Override public void add_flow_use_extra(Node chg) {
    if( chg instanceof CallNode ) {    // If the Call changes value
      Env.GVN.add_flow(chg.in(MEM_IDX));       // The called memory   changes liveness
      Env.GVN.add_flow(((CallNode)chg).fdx()); // The called function changes liveness
    }
  }

  @Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
}
