package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MProjNode extends ProjNode {

  public MProjNode( Node head ) { super(head, MEM_IDX); }
  public MProjNode( Node head, int idx ) { super(head,idx); }
  @Override public String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }

  @Override public void add_flow_def_extra(Node chg) {
    // Dropping last mem use enables Store folding into New
    if( in(0) instanceof NewNode )
      for( Node use : _uses )
        if( use instanceof StoreNode )
          Env.GVN.add_reduce(use);
  }
  @Override public void add_flow_use_extra(Node chg) {
    if( chg instanceof CallNode ) {    // If the Call changes value
      Env.GVN.add_flow(chg.in(MEM_IDX));       // The called memory   changes liveness
      Env.GVN.add_flow(((CallNode)chg).fdx()); // The called function changes liveness
    }
    if( chg instanceof NewNode nnn && chg._uses._len==1 && nnn.rec()==Env.UNUSED )
      Env.GVN.add_reduce(this);
  }

  @Override public Type live_use( Node def ) { return _live; }

  @Override public Node ideal_reduce() {
    // Fold dying calls
    Node mem = in(0).is_copy(MEM_IDX);
    if( mem != null )
      return mem;

    // Allocation has no ptr uses, so is dead, so drop
    if( in(0) instanceof NewNode nnn && nnn._uses._len==1 ) {
      TypeMem tnnn = (TypeMem)((TypeTuple)nnn._val).at(1);
      TypeStruct tns = tnnn.at(nnn._alias);
      // All memory has to be monotonic; easiest to require all the same
      if( tnnn==_val && tnnn==nnn.mem()._val && tns==TypeStruct.UNUSED )
        return nnn.mem();
    }
    return null;
  }
}
