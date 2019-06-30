package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeMemPtr;
import com.cliffc.aa.type.TypeObj;

// Merge a TypeObj at address TypeMemPtr into a TypeMem.
public class MemMergeNode extends Node {
  public MemMergeNode( Node mem, Node obj, Node ptr ) { super(OP_MERGE,mem,obj,ptr);  }
  Node mem() { return in(0); }
  private Node obj() { return in(1); }
  private Node ptr() { return in(2); }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If merging from a NewNode, and the NewNode is a dead_address then the
    // memory contents cannot be looked at, and are also dead.
    if( obj().in(0) instanceof NewNode &&
        ptr().in(0) == obj().in(0) &&
        ptr()._uses._len==1 )   // Nobody uses the pointer, except this
      return in(0);             // Skinny memory is dead, nothing to merge
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type mem = gvn.type(mem());
    Type obj = gvn.type(obj());
    Type ptr = gvn.type(ptr());
    if( mem instanceof TypeMem &&
        obj instanceof TypeObj &&
        ptr instanceof TypeMemPtr )
      // Compute a precise memory update
      return ((TypeMem)mem).st((TypeObj)obj,(TypeMemPtr)ptr);
    return TypeMem.MEM;
  }
  @Override public Type all_type() { return TypeMem.MEM; }

  // Return the exact NewNode, or null
  NewNode exact( Node ptr ) {
    Node nn = obj().in(0);
    return ptr()==ptr && nn instanceof NewNode ? (NewNode)nn : null;
  }
  
}

