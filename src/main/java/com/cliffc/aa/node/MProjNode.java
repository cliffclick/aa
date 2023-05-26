package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.BitsFun;
import com.cliffc.aa.type.Type;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MProjNode extends ProjNode {

  public MProjNode( Node head ) { this(head, MEM_IDX); }
  public MProjNode( Node head, int idx ) {
    super(head,idx);
    _live=RootNode.def_mem(null);
  }
  @Override public String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }

  @Override public Type live_use( int i ) { return _live; }

  @Override public Node ideal_reduce() {
    if( is_prim() ) return null;
    // Fold dying calls
    Node mem = in(0).is_copy(MEM_IDX);
    if( mem != null )
      return mem==this ? Env.ANY : mem;

    // Fold across pure calls (most primitives)
    if( in(0) instanceof CallEpiNode cepi ) {
      CallNode call = cepi.call();
      if( call.tfp()._fidxs!=BitsFun.NALL && cepi.nwired()>0 ) {
        boolean pure=true;
        for( int i=0; i<cepi.nwired(); i++ ) {
          Node w = cepi.wired(i);
          if( w instanceof RetNode ret ) {
            if( ret.mem()!=null ) { ret.deps_add(this); pure=false;  break; }
          } else { pure=false;  break; }
        }      
        if( pure )
          return call.mem();
      } else {
        call.deps_add(this);    // Call sharpens, can fold
      }
    }

    return null;
  }

  @Override public boolean has_tvar() { return false; }
}
