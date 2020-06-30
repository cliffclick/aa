package com.cliffc.aa.node;

import com.cliffc.aa.Env;
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
    if( _defs._len > 3 ) throw com.cliffc.aa.AA.unimpl(); // Handle more than one set
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

    // Pick left or right and merge (not meet)
    TypeObj[] tos = new TypeObj[Env.DEFMEM._defs._len];
    for( int alias=1; alias<tos.length; alias++ ) {
      TypeObj tl = tpre.at(alias);
      TypeObj tr = trhs.at(alias);
      tos[alias] = tl==TypeObj.ISUSED ? tl // 'use' always LHS
        : (tl==TypeObj.UNUSED ? tr         // '~use' always RHS
           : (aliases.test_recur(alias) ? tr : tl)); // Otherwise pick from escapes
    }
    return TypeMem.make0(tos);
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
