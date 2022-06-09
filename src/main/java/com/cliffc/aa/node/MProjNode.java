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

  @Override public void add_flow_use_extra(Node chg) {
    if( chg instanceof CallNode ) {    // If the Call changes value
      Env.GVN.add_flow(chg.in(MEM_IDX));       // The called memory   changes liveness
      Env.GVN.add_flow(((CallNode)chg).fdx()); // The called function changes liveness
    }
  }

  @Override public Type live_use( Node def ) { return _live; }
}
