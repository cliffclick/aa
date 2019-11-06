package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.AA;
import com.cliffc.aa.type.*;

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

    // if Skinny memory is XMEM, then merging nothing and remove self
    Node mem = mem();
    if( gvn.type(obj())==TypeMem.XMEM )
      return mem;
    // If skinny is a pointer and not memory, then this is a collapsing
    // named-type-into-allocator.
    if( gvn.type(obj()) instanceof TypeMemPtr )
      return mem;

    // Back-to-back merges collapse, same as back-to-back stores
    if( mem instanceof MemMergeNode ) {
      MemMergeNode mem2 = (MemMergeNode)mem;
      if( obj() == mem2.obj() )
        return mem2;
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type mem = gvn.type(mem());
    Type obj = gvn.type(obj());
    if( !(mem instanceof TypeMem) || !(obj instanceof TypeObj) )
      return mem.above_center() ? TypeMem.XMEM : TypeMem.MEM;
    TypeMem wm2 = (TypeMem)mem;
    TypeObj nm2 = (TypeObj)obj;
    return wm2.update(nm2);
  }
  @Override public Type all_type() { return TypeMem.MEM; }

  // Return the exact NewNode, or null
  NewNode exact( Node ptr ) {
    return ptr.in(0)==obj().in(0) && ptr.in(0) instanceof NewNode ? (NewNode)ptr.in(0) : null;
  }

  // Split this node into a set returning 'bits' and the original which now
  // excludes 'bits'.  Return null if already making a subset of 'bits'.
  Node split_memory_use( GVNGCM gvn, BitsAlias bits ) {
    TypeMem t = (TypeMem)gvn.type(this);
    Type tm2 = gvn.type(mem());
    Type to2 = gvn.type(obj());
    if( to2 == TypeMem.XMEM ) return null; // Happens when folding up dead NewNode in MemMerge
    if( !(to2 instanceof TypeObj) ) return null;
    TypeMem tm= tm2==Type.ANY ? TypeMem.XMEM : (TypeMem)tm2;
    TypeObj to= (TypeObj)to2;
    assert t==TypeMem.XMEM || t.contains(bits);

    if( bits.isa(to._news) || to._news.isa(bits) ) { // Test if bits is in narrow memory
      if( tm.contains(bits) ) {
        return null;            // Since it contains both, some stronger alias analysis is needed to bypass
      } else {
        return obj();           // Tighten in on narrow memory
      }
    } else {
      if( tm.contains(bits) ) { // Not in narrow memory, test wide
        return mem();           // tighten on wide memory
      } else {
        throw AA.unimpl();      // neither, value must go XSCALAR
      }
    }
  }
}

