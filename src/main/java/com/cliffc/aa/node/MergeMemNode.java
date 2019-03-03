package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

public class MergeMemNode extends Node {
  public MergeMemNode( Node wide, Node skinny ) { super(OP_MERGE,wide,skinny); }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If the skinny memory is from a MProj from a NewNode, and the only proj
    // is the MProj, then there is no *address* user, and the New object must
    // be dead.  Remove the New.
    if( in(1) instanceof MProjNode &&
        in(1).in(0) instanceof NewNode &&
        in(1).in(0)._uses._len==1 )
      return in(0);             // Skinny memory is dead, nothing to merge
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    return TypeMem.MEM;
  }
  
  @Override public Type all_type() { return TypeMem.MEM; }
  @Override public int hashCode() { return OP_MERGE; }
  // Stores are never CSE/equal lest we force a partially-execution to become a
  // total execution (require a store on some path it didn't happen).  Stores
  // that are common in local SESE regions can be optimized with local peepholes.
  @Override public boolean equals(Object o) { return this==o; }
}

