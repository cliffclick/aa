package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Split a set of aliases into a SESE region, to be joined by a later MemJoin.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemSplitNode extends Node {

  final BitsAlias _split; // Aliases split on MProj#1; the unnamed ones are on MProj#0
  public MemSplitNode( Node allmem, BitsAlias split, TypeMem live ) { super(OP_SPLIT,allmem); _split=split; _live=live; }

  @Override String str() { return "Split"+_split; }
  @Override public int hashCode() { return super.hashCode()+_split.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof MemSplitNode) ) return false;
    MemSplitNode parm = (MemSplitNode)o;
    return _split==parm._split;
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    if( _defs._len!=1 ) return null; // Already is_copy
    // Push Split up, to keep widening memory (increasing precision)
    if( in(0) instanceof MemMergeNode )
      return bypass_merge(gvn,(MemMergeNode)in(0));

    // If split to the program root, then all is already max split
    if( in(0)==Env.MEM_0 && _uses._len==1 )
      return add_def(Env.MEM_0); // Trigger is_copy
    
    return null;
  }

  // Was: Merge/oldSplit/{MPrj0,MPrj1}
  // Becomes: newSplit/{MPrj0n/Merge0,oldSplit},MPrj0n/Merge1,oldSplit};
  private Node bypass_merge(GVNGCM gvn, MemMergeNode mem) {
    // New split from Merge base
    MemSplitNode nsplit = (MemSplitNode)gvn.xform(new MemSplitNode(mem.mem(),_split,_live));
    Node m0n = gvn.xform(new MProjNode(nsplit,0));  m0n._live = _live;
    Node m1n = gvn.xform(new MProjNode(nsplit,1));  m1n._live = _live;
    // Two merges, one for left and one for right
    MemMergeNode lhs = new MemMergeNode(m0n);
    MemMergeNode rhs = new MemMergeNode(m1n);
    // Constants for the split
    Node xobj = gvn.con(TypeObj.XOBJ);
    Node xuse = gvn.con(TypeObj.UNUSED);
    TypeMem tsplit = (TypeMem)gvn.type(mem);

    // Feed alias edges to the merges, left or right
    int max = Math.max(_split.max()+1,tsplit.len());
    for( int alias=2; alias<max; alias++ ) {
      Node base = mem.alias2node(alias); // Alias node from base
      Node yobj = tsplit.at(alias)==TypeObj.XOBJ ? base : xobj; // XOBJ either way, but from base or a constant
      Node yuse = tsplit.at(alias)==TypeObj.XOBJ ? base : xuse; // XUSE either way, but from base or a constant
      Node l,r;
      if( tsplit.at(alias)==TypeObj.UNUSED ) {
        l = r = yuse;
      } else if( _split.test_recur(alias) ) { // Alias splits right
        l=yobj; r=base;
      } else {                  // Alias splits left
        l=base; r=yobj;
      }
      lhs.create_alias_active(alias,l,gvn);
      rhs.create_alias_active(alias,r,gvn);
    }
    Node nlhs = gvn.xform(lhs); nlhs._live = _live;
    Node nrhs = gvn.xform(rhs); nrhs._live = _live;
    // Set both inputs, turning 'this' into a copy.
    set_def(0,nlhs,gvn);
    add_def(nrhs);
    return this;
  }

  @Override public Type value(GVNGCM gvn) {
    Type t0 = gvn.type(in(0));
    if( !(t0 instanceof TypeMem) ) return t0.oob();
    return TypeTuple.make( t0, ((TypeMem)t0).split_by_alias(_split));
  }
  @Override public boolean basic_liveness() { return false; }

  // If two inputs, we are a copy.
  @Override public Node is_copy(GVNGCM gvn, int idx) { return _defs._len==1 ? null : in(idx); }
}
