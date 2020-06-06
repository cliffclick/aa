package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Join a split set of aliases from a SESE region, split by an earlier MemSplit.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemJoinNode extends Node {

  final BitsAlias _split;
  public MemJoinNode( Node lhs, Node rhs, Node defmem, BitsAlias split, TypeMem live ) { super(OP_JOIN,lhs,rhs, defmem); _split=split; _live=live; }

  @Override String str() { return "Join"+_split; }
  @Override public int hashCode() { return super.hashCode()+_split.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof MemJoinNode) ) return false;
    MemJoinNode parm = (MemJoinNode)o;
    return _split==parm._split;
  }
  @Override public Node ideal(GVNGCM gvn, int level) {

    Node mem0 = in(0);
    Node mpj0 = mem0 instanceof MemMergeNode ? mem0.in(0) : mem0;

    Node mem1 = in(1);
    Node mpj1 = mem1 instanceof MemMergeNode ? mem1.in(0) : mem1;

    // Empty split?
    Node s00 = mpj0.in(0);
    MemSplitNode split;
    if( mpj1.in(0)==s00 && s00 instanceof MemSplitNode && (split=(MemSplitNode)s00)._split==_split &&
        mpj0 instanceof MProjNode && ((MProjNode)mpj0)._idx==0 &&
        mpj1 instanceof MProjNode && ((MProjNode)mpj1)._idx==1 &&
        mem0._uses._len==1 && mem1._uses._len==1 ) {

      if( mem0==mpj0 && mem1==mpj1 ) // Just return the split base
        return split.in(0);

      MemMergeNode mmm0 = mem0 instanceof MemMergeNode ? (MemMergeNode)mem0 : null;
      MemMergeNode mmm1 = mem1 instanceof MemMergeNode ? (MemMergeNode)mem1 : null;
      TypeMem tmem0 = (TypeMem)gvn.type(mem0);
      TypeMem tmem1 = (TypeMem)gvn.type(mem1);
      TypeMem defmem= (TypeMem)gvn.type(in(2));

      int len = ((TypeMem)gvn.type(this)).len();
      if( mmm0 != null ) len = Math.max(len,mmm0.max()+1);
      if( mmm1 != null ) len = Math.max(len,mmm1.max()+1);

      // Same algo as merge_by_alias, merge_one_lhs, merge_pick.
      MemMergeNode mem = new MemMergeNode(split.in(0));
      for( int alias=2; alias<len; alias++ ) {
        TypeObj rhs = tmem1.at(alias);
        Node n = tmem0.merge_one_lhs(_split,alias,rhs) == rhs
          ? (mmm1==null ? mem1 : mmm1.alias2node(alias))
          : (mmm0==null ? mem0 : mmm0.alias2node(alias));
        if( defmem.at(alias)==TypeObj.UNUSED && gvn.type(n) != TypeObj.UNUSED )
          n = split.in(0);
        mem.create_alias_active(alias,n,gvn);
      }
      return mem;
    }

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type lhs = gvn.type(in(0));
    Type rhs = gvn.type(in(1));
    if( !(lhs instanceof TypeMem) ) return lhs.oob();
    if( !(rhs instanceof TypeMem) ) return rhs.oob();

    // Merge types left and right
    TypeMem trez = ((TypeMem)lhs).merge_by_alias((TypeMem)rhs,_split);
    // Lift to UNUSED, if required.  This is basically a shortcut
    // because nearly always the join is useless.
    TypeMem defmem = (TypeMem)gvn.type(in(2));
    for( int alias=2; alias<trez.len(); alias++ )
      if( defmem.at(alias)==TypeObj.UNUSED && trez.at(alias)!=TypeObj.UNUSED )
        return trez.join(defmem);

    return trez;
  }
  @Override public boolean basic_liveness() { return false; }

  // Some memory user can bypass, if the aliases are compatible
  Node can_bypass( GVNGCM gvn, TypeMemPtr tmp ) {
    // Check for easy split right
    if( tmp._aliases.isa(_split) ) return in(1);
    // Check for split left, but LHS has no answer and RHS made a New
    TypeMem lhs = (TypeMem)gvn.type(in(0));
    TypeMem rhs = (TypeMem)gvn.type(in(1));
    TypeObj lld = lhs.ld(tmp);
    TypeObj rld = rhs.ld(tmp);
    if( TypeMem.merge_pick(lld,rld)==rld )
      return in(1);
    // Check for easy split left
    if( tmp._aliases.join(_split).is_empty() )
      return in(0);
    return null;
  }

}
