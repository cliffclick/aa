package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeMemPtr;

// Merge a TypeObj at address TypeMemPtr into a TypeMem.
public class MemMergeNode extends Node {
  public MemMergeNode( Node mem, Node ptr ) { super(OP_MERGE,mem,ptr);  }
  private Node mem() { return in(0); }
  private Node ptr() { return in(1); }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If I have a Named Constructor usage, and have 2 uses (named constructor
    // and the Merge following it), make sure the Named Constructor can run
    // ideal() so it can fold away.
    if( _uses._len==2 )
      for( Node use : _uses )
        if( use instanceof IntrinsicNode.ConvertPtrTypeName )
          gvn.add_work(use);
    
    // If merging from a NewNode, and the NewNode's address is not looked at
    // then memory contents cannot be looked at and are also dead.
    if( ptr() instanceof NewNode &&
        ptr()._uses._len==1  && // Nobody uses the pointer, except this
        ptr()._keep == 0 )      // Including future parser uses
      return in(0);             // Skinny memory is dead, nothing to merge

    // Back-to-back merges collapse, same as back-to-back stores
    if( mem() instanceof MemMergeNode ) {
      MemMergeNode mem = (MemMergeNode)mem();
      if( ptr() == mem.ptr() )
        return mem();
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type mem = gvn.type(mem());
    Type ptr = gvn.type(ptr());
    if( mem instanceof TypeMem &&
        ptr instanceof TypeMemPtr )
      // Compute a precise memory update
      return ((TypeMem)mem).st((TypeMemPtr)ptr);
    return TypeMem.MEM;
  }
  @Override public Type all_type() { return TypeMem.MEM; }

  // Return the exact NewNode, or null
  NewNode exact( Node ptr ) {
    return ptr==ptr() && ptr() instanceof NewNode ? (NewNode)ptr() : null;
  }
  
}

