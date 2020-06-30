package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Join a split set of aliases from a SESE region, split by an earlier MemSplit.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemJoinNode extends Node {

  public MemJoinNode( Node lhs, Node rhs, Node escapees ) { super(OP_JOIN,lhs,rhs,escapees); }

  Node pre() { return in(0); }  // pre-split & non-escape memory
  Node rhs() { return in(1); }  // post-split escaped memory
  Node esc() { return in(2); }  // Node controlling escaped aliases from v-call

  @Override public Node ideal(GVNGCM gvn, int level) {
    //// Empty split?
    //MemSplitNode msp = msp();
    //if( msp == null ) return null;
    //if( msp==in(1).in(0) )
    //  return msp.mem();
    //
    //// Nearly empty split - just a MemMerge.
    //// MemJoin.1 -> MemMerge.0 -> MProj.0 -> MemSplit
    //MemMergeNode mmm;  Node base;
    //if( in(1) instanceof MemMergeNode &&
    //    (base=(mmm=((MemMergeNode)in(1))).mem()) instanceof MProjNode &&
    //    msp==base.in(0) &&
    //    base._uses.find(e->e!=mmm)!=-1 )
    //  // "Swap" MemJoin and MemMerge, and nuke MemJoin/MemSplit pair
    //  return mmm.copy(true,gvn).set_def(0,msp.mem(),gvn);
    //
    //// Nearly empty split - just a Name
    //// MemJoin.1 -> Name.0 -> MProj.0 -> MemSplit
    //IntrinsicNode isn;
    //if( in(1) instanceof IntrinsicNode &&
    //    (base=(isn=((IntrinsicNode)in(1))).mem()) instanceof MProjNode &&
    //    msp==base.in(0) &&
    //    base._uses.find(e->e!=isn)!=-1 )
    //  // "Swap" MemJoin and Name, and nuke MemJoin/MemSplit pair
    //  return isn.copy(true,gvn).set_def(1,msp.mem(),gvn);

    return null;
  }

  // Merges left & right memories based on alias escapees.
  //  use always goes-left  (pre -split only).
  // ~use always goes-right (post-split only).
  // Others use the escapee set, which monotonically decreases over time.
  @Override public Type value(GVNGCM gvn) {
    Type pre = gvn.type(pre());
    Type rhs = gvn.type(rhs());
    if( !(pre instanceof TypeMem) ) return pre.oob();
    if( !(rhs instanceof TypeMem) ) return rhs.oob();
    TypeMem tpre = (TypeMem)pre;
    TypeMem trhs = (TypeMem)rhs;
    BitsAlias aliases = esc().escapees();

    for( int alias : aliases )
      assert tpre.at(alias)!=TypeObj.ISUSED; // All 'use' do not escape, go left
    for( int alias=2; alias<tpre.len(); alias++ )
      assert tpre.at(alias)!=TypeObj.UNUSED || aliases.test_recur(alias);

    // All ~use always goes-right
    if( tpre == TypeMem.ANYMEM) return trhs;

    //Type msp = gvn.type(msp());
    //if( !(msp instanceof TypeTuple) ) return msp.oob();
    //TypeTuple tmsp = (TypeTuple)msp;
    //BitsAlias as = ((TypeMemPtr)(tmsp.at(2)))._aliases;
    //if( as==BitsAlias.FULL || as==BitsAlias.NZERO ) return rhs;
    //TypeMem precall_mem = (TypeMem)tmsp.at(0); // Pre-call memory
    //TypeMem defmem = (TypeMem)gvn.type(in(2));
    //// Since the RHS will have a call, all its memory is JOINed with DEFMEM
    //// already.  If any alias moves from Right to Left, the LHS now needs to be
    //// joined with DEFMEM also.
    //TypeMem tmem = (TypeMem)precall_mem.join(defmem);
    //// Replace pre-call with RHS on escaping aliases
    //for( int alias : as )
    //  for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) )
    //    tmem = tmem.set(kid,trhs.at(kid));
    //// Replace pre-call with RHS, where LHS is ~obj and RHS is != ~use.
    //// This catches RHS fresh allocations.
    //TypeMem tmem2 = tmem;
    //for( int alias=2; alias<tmem.len(); alias++ ) {
    //  if( tmem.at(alias)==TypeObj.XOBJ && trhs.at(alias)!=TypeObj.UNUSED )
    //    tmem2 = tmem2.set(alias,trhs.at(alias));
    //}
    //
    //return tmem2;

    // Expect pairs of RHS-memory and RHS-aliases; RHS-aliases supports v-call for aliases.
    throw com.cliffc.aa.AA.unimpl();
  }
  @Override public boolean basic_liveness() { return false; }

  // Some memory user can bypass, if the aliases are compatible
  Node can_bypass( GVNGCM gvn, TypeMemPtr tmp ) {
    //MemSplitNode msp = msp();
    //if( msp == null ) return null;
    //Type tmsp = gvn.type(msp());
    //if( !(tmsp instanceof TypeTuple) ) return null;
    //TypeTuple tt = (TypeTuple)tmsp;
    //TypeMem lmm = (TypeMem)tt.at(0);
    //TypeMem rmm = (TypeMem)tt.at(1);
    //TypeObj lld = lmm.ld(tmp);
    //TypeObj rld = rmm.ld(tmp);
    //
    //if( rld==TypeObj.UNUSED )
    //  return in(0);
    //if( lld==TypeObj.UNUSED )
    //  return in(1);
    //return null;
    throw com.cliffc.aa.AA.unimpl();
  }
}
