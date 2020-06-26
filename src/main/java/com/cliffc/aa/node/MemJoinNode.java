package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Join a split set of aliases from a SESE region, split by an earlier MemSplit.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemJoinNode extends Node {

  public MemJoinNode( MProjNode lhs, Node rhs ) { super(OP_JOIN,lhs,rhs); }

  MemSplitNode msp() {
    if( !(in(0) instanceof MProjNode) ) return null;
    if( !(in(0).in(0) instanceof MemSplitNode) ) return null;
    return (MemSplitNode)in(0).in(0);
  }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // Empty split?
    MemSplitNode msp = msp();
    if( msp == null ) return null;
    if( msp==in(1).in(0) )
      return msp.mem();

    // Nearly empty split - just a MemMerge
    MemMergeNode mmm;  Node base;
    if( in(1) instanceof MemMergeNode &&
        (base=(mmm=((MemMergeNode)in(1))).mem()) instanceof MProjNode &&
        msp==base.in(0) )
      return gvn.set_def_reg(mmm,0,msp.mem());

    // Nearly empty split - just a Name
    IntrinsicNode isn;
    if( in(1) instanceof IntrinsicNode &&
        (base=(isn=((IntrinsicNode)in(1))).mem()) instanceof MProjNode &&
        msp==base.in(0) )
      return gvn.set_def_reg(isn,0,msp.mem());

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type lhs = gvn.type(in(0));
    Type rhs = gvn.type(in(1));
    if( !(lhs instanceof TypeMem) ) return lhs.oob();
    if( !(rhs instanceof TypeMem) ) return rhs.oob();
    assert lhs==TypeMem.ANYMEM;
    return rhs;
  }
  @Override public boolean basic_liveness() { return false; }

  // Some memory user can bypass, if the aliases are compatible
  Node can_bypass( GVNGCM gvn, TypeMemPtr tmp ) {
    //// Check for easy split right
    //if( tmp._aliases.isa(NewNode.ESCAPES) ) return in(1);
    //// Check for split left, but LHS has no answer and RHS made a New
    //TypeMem lhs = (TypeMem)gvn.type(in(0));
    //TypeMem rhs = (TypeMem)gvn.type(in(1));
    //TypeObj lld = lhs.ld(tmp);
    //TypeObj rld = rhs.ld(tmp);
    //if( TypeMem.merge_pick(lld,rld)==rld )
    //  return in(1);
    //// Check for easy split left
    //if( !tmp._aliases.overlap(NewNode.ESCAPES) )
    //  return in(0);
    //return null;
    throw com.cliffc.aa.AA.unimpl();
  }
}
