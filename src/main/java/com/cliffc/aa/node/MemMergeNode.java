package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeObj;

// Merge a TypeObj at address TypeMemPtr into a TypeMem.
public class MemMergeNode extends Node {
  public MemMergeNode( Node mem, Node ptr ) { super(OP_MERGE,mem,ptr);  }
  Node mem() { return in(0); } // Wide mem
  Node obj() { return in(1); } // Narrow mem, merging into wide

  @Override public Node ideal(GVNGCM gvn) {
    // If I have a Named Constructor usage, and have 2 uses (named constructor
    // and the Merge following it), make sure the Named Constructor can run
    // ideal() so it can fold away.
    if( _uses._len==2 )
      for( Node use : _uses )
        if( use instanceof IntrinsicNode.ConvertPtrTypeName )
          gvn.add_work(use);
    // Following store and is the only use
    if( _uses._len==1 && _uses.at(0) instanceof StoreNode )
      gvn.add_work(_uses.at(0));

    // If merging from a NewNode, and the NewNode's address is not looked at
    // then memory contents cannot be looked at and are also dead.
    Node obj = obj(), nnew = obj.in(0), mem = mem();
    if( obj instanceof OProjNode &&
        nnew instanceof NewNode &&
        nnew._uses._len==1  &&  // Nobody uses the pointer, except this
        nnew._keep == 0 )       // Including future parser uses
      return mem;               // Skinny object is dead, nothing to merge

    // Back-to-back merges collapse, same as back-to-back stores
    if( mem instanceof MemMergeNode ) {
      MemMergeNode mem2 = (MemMergeNode)mem;
      if( obj() == mem2.obj() )
        //  return mem2;
        throw com.cliffc.aa.AA.unimpl();
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type mem = gvn.type(mem());
    Type obj = gvn.type(obj());
    if( !(mem instanceof TypeMem) || !(obj instanceof TypeObj) )
      return TypeMem.MEM;
    TypeMem wm2 = (TypeMem)mem;
    TypeObj nm2 = (TypeObj)obj;
    return wm2.update(nm2);
  }
  @Override public Type all_type() { return TypeMem.MEM; }

  // Return the exact NewNode, or null
  NewNode exact( Node ptr ) {
    return ptr.in(0)==obj().in(0) && ptr.in(0) instanceof NewNode ? (NewNode)ptr.in(0) : null;
  }

}

