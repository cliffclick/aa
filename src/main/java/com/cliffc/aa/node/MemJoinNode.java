package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

// Join a split set of aliases from a SESE region, split by an earlier MemSplit.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemJoinNode extends Node {

  public MemJoinNode( MProjNode mprj ) { super(OP_JOIN,mprj); assert mprj.in(0) instanceof MemSplitNode; }

  MemSplitNode msp() { return (MemSplitNode)in(0).in(0); }  // The MemSplit
  @Override boolean is_mem() { return true; }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If the split count is lower than 2, then the split serves no purpose
    if( _defs._len == 2 ) return in(1); // Just become the last split

    // If the Split memory has an obvious SESE region, move it into the Split
    MemSplitNode msp = msp();
    Node mem = msp.mem();
    if( mem instanceof MProjNode && mem.in(0) instanceof NewNode && !mem.is_prim() &&
        msp().mem().check_solo_mem_writer(msp()) ) { // Split is only memory writer after base
      assert level==0;
      // Since NewNodes are 1 alias only, they always can move inside.
      return add_alias_above(gvn, mem.in(0));
    }

    // If some Split/Join path clears out, remove the (useless) split.
    for( int i=1; i<_defs._len; i++ )
      if( in(i) instanceof MProjNode && in(i).in(0)==msp ) {
        msp.remove_alias(gvn,i);
        return remove(i,gvn);
      }

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    // Gather all memories
    boolean diff=false;
    TypeMem[] mems = new TypeMem[_defs._len];
    for( int i=0; i<_defs._len; i++ ) {
      Type t = gvn.type(in(i));
      if( !(t instanceof TypeMem) ) return t.oob(TypeMem.ALLMEM);
      mems[i] = (TypeMem)t;
      if( i>0 && !diff ) diff = mems[i]!=mems[0];
    }
    if( !diff ) return mems[0]; // All memories the same

    // Walk all aliases and take from matching escape set in the Split.  Since
    // nothing overlaps this is unambiguous.
    Ary<BitsAlias> escs = msp()._escs;
    TypeObj[] tos = new TypeObj[Env.DEFMEM._defs._len];
    for( int alias=1, i; alias<tos.length; alias++ ) {
      if( escs.at(0).test_recur(alias) ) { // In some RHS set
        for( i=1; i<_defs._len; i++ )
          if( escs.at(i).test_recur(alias) )
            break;
      } else i=0;                     // In the base memory
      tos[alias] = mems[i].at(alias); // Merge alias
    }
    return TypeMem.make0(tos);
  }
  @Override public boolean basic_liveness() { return false; }

  // Move the given SESE region just ahead of the split into the join/split
  // area.  The head node has the escape-set.
  MemJoinNode add_alias_above( GVNGCM gvn, Node head ) {
    MemSplitNode msp = msp();
    Node base = msp.mem();                  // Base of SESE region
    assert base.check_solo_mem_writer(msp); // msp is only memory writer after base
    assert head.in(1).check_solo_mem_writer(head); // head is the 1 memory writer after head.in
    int idx = msp.add_alias(gvn,head.escapees(gvn)), bidx; // Add escape set, find index
    Node mprj, body;
    if( idx == _defs._len ) {         // Escape set added at the end
      add_def(mprj = gvn.xform(new MProjNode(msp,idx))); // Add a new MProj from MemSplit
      body = this;              // Head of inside-body region is just 'this'
      bidx = idx;               // Memory input from Join to MProj
    } else {
      assert idx!=0;     // No partial overlap; all escape sets are independent
      mprj = ProjNode.proj(msp,idx); // Find match MProj
      body = mprj.get_mem_writer();
      bidx = 1;                 // Standard memory input
    }
    // Resort edges to move SESE region inside
    assert mprj.check_solo_mem_writer(body);
    mprj.keep();
    if( body==this ) set_def(bidx,base,gvn);
    else gvn.set_def_reg(body,bidx,base); // Move body.mem -> base
    gvn.set_def_reg(msp,1,head.in(1)); // Move Split->base edge to Split->head.in(1)
    gvn.set_def_reg(head,1,mprj.unhook()); // Move head->head.in(1) to head->MProj
    // Moving things inside the Split/Join region might let types get
    // out-of-order; the Split might be able to lift and be stale, while the
    // moved body is on the 'wrong side' of the stale Split.  Update the Split
    // and following MProjNodes immediately.
    Type tmsp_old = gvn.type(msp);
    Type tmsp_new = msp.value(gvn);
    gvn.setype(msp,tmsp_new);    // Moving a region 'inside' might lift the Split
    for( Node use : msp._uses ) {// Also lift all MProjs
      gvn.setype(use,use.value(gvn));
      use._live = use.live(gvn); // Also might lower all _live sets
      if( tmsp_old!=tmsp_new )  // If the Split moved, the MProjs also moved
        gvn.add_work_uses(use); // And if they moved, revisit the interior
    }
    msp._live = msp.live(gvn);
    return this;
  }

  // Move the given SESE region just behind of the join into the join/split
  // area.  The head node has the escape-set.
  MemJoinNode add_alias_below( GVNGCM gvn, Node head, Node base, Node base_memw ) {
    assert head.is_mem() && base.is_mem();
    MemSplitNode msp = msp();
    int idx = msp.add_alias(gvn,head.escapees(gvn)), bidx; // Add escape set, find index
    if( idx == _defs._len ) {         // Escape set added at the end
      throw com.cliffc.aa.AA.unimpl();
    } else {                    // Inserted into prior region
      assert idx!=0;     // No partial overlap; all escape sets are independent
    }
    // Reset edges to move SESE region inside
    keep();
    gvn.set_def_reg(head,1,in(idx));
    gvn.set_def_reg(this,idx,base);
    gvn.set_def_reg(base_memw,1,this);
    return unhook();
  }

  // Find a compatible alias edge, including base memory if nothing overlaps.
  // Return null for any partial overlaps.
  Node can_bypass( BitsAlias esc ) {
    Ary<BitsAlias> escs = msp()._escs;
    if( escs.at(0).join(esc)==BitsAlias.EMPTY ) // No overlap with any other alias set
      return msp().mem();                       // Can completely bypass
    // Overlaps with at least 1
    for( int i=1; i<escs._len; i++ )
      if( esc.isa(escs.at(i)) ) // Fully contained with alias set 'i'?
        return in(i);           // Can use this memory
    return null;                // Not fully contained within any 1 alias set
  }
  // Modifies all of memory
  @Override BitsAlias escapees(GVNGCM gvn) { return BitsAlias.FULL; }
}
