package com.cliffc.aa.node;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MProjNode extends ProjNode {

  public MProjNode( Node head ) { this(head, MEM_IDX); }
  public MProjNode( Node head, int idx ) { super(head,idx); _live=TypeMem.ALLMEM; }
  @Override public String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }

  @Override public Type live_use( Node def ) { return _live; }

  @Override public Node ideal_reduce() {
    // Fold dying calls
    Node mem = in(0).is_copy(MEM_IDX);
    if( mem != null )
      return mem;

    // Fold across pure calls (most primitives)
    if( in(0) instanceof CallEpiNode cepi && cepi.is_all_wired() ) {
      boolean pure=true;
      for( int i=0; i<cepi.nwired(); i++ )
        if( cepi.wired(i).mem()!=null )
          { pure=false; break; }
      if( pure )
        return cepi.call().mem();
    }
    
    return null;
  }
}
