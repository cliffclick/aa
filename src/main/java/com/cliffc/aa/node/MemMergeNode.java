package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeMemPtr;
import com.cliffc.aa.type.TypeObj;

// Merge a TypeObj at address TypeMemPtr into a TypeMem.
public class MemMergeNode extends Node {
  public MemMergeNode( Node mem, Node obj, Node ptr ) { super(OP_MERGE,mem,obj,ptr);  }
  @Override public Node ideal(GVNGCM gvn) {
    // If merging from a NewNode, and the NewNode is a dead_address then the
    // memory contents cannot be looked at, and are also dead.
    if( in(1) instanceof ProjNode &&
        in(1).in(0) instanceof NewNode &&
        ((NewNode)in(1).in(0)).is_dead_address() )
      return in(0);             // Skinny memory is dead, nothing to merge
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type mem = gvn.type(in(0));
    Type obj = gvn.type(in(1));
    Type ptr = gvn.type(in(2));
    if( mem instanceof TypeMem &&
        obj instanceof TypeObj &&
        ptr instanceof TypeMemPtr )
      // Compute a precise memory update
      return ((TypeMem)mem).st((TypeObj)obj,(TypeMemPtr)ptr);
    return TypeMem.MEM;
  }
  @Override public Type all_type() { return TypeMem.MEM; }
}

