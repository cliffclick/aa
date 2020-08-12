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
  @Override public boolean is_mem() { return true; }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If the split count is lower than 2, then the split serves no purpose
    if( _defs._len == 2 && gvn.type(in(1)).isa(gvn.self_type(this)) && _keep==0 )
      return in(1);             // Just become the last split

    // If some Split/Join path clears out, remove the (useless) split.
    MemSplitNode msp = msp();
    for( int i=1; i<_defs._len; i++ )
      if( in(i) instanceof MProjNode && in(i).in(0)==msp ) {
        gvn.setype(in(0),in(0).value(gvn)); // Update the default type
        msp.remove_alias(gvn,i);
        return remove(i,gvn);
      }

    // If the Split memory has an obvious SESE region, move it into the Split
    Node mem = msp.mem();
    if( !mem.is_prim() && mem.check_solo_mem_writer(msp) ) { // Split is only memory writer after mem
      Node head = find_sese_head(mem);                       // Find head of SESE region
      if( head instanceof MemSplitNode )                     // Back to back split/join combo
        return combine_splits(gvn,(MemSplitNode)head);
      if( head != null && head.in(1).check_solo_mem_writer(head) ) // Head is the only writer after the above-head
        // Move from Split.mem() to head inside the split/join area
        return add_alias_above(gvn, head);
    }

    return null;
  }

  private Node find_sese_head(Node mem) {
    if( mem instanceof MemJoinNode ) return ((MemJoinNode)mem).msp(); // Merge Split with prior Join
    if( mem instanceof StoreNode ) return mem;   // Move Store into Split/Join
    if( mem instanceof MProjNode ) {
      Node head = mem.in(0);
      if( head instanceof CallNode ) return null; // Do not swallow a Call/CallEpi into a Split/Join
      if( head instanceof CallEpiNode ) return null; // Do not swallow a Call/CallEpi into a Split/Join
      if( head instanceof MemSplitNode ) return null; // TODO: Handle back-to-back split/join/split/join
      throw com.cliffc.aa.AA.unimpl(); // Break out another SESE split
    }
    if( mem instanceof MrgProjNode ) return mem;
    if( mem instanceof ParmNode ) return null;
    if( mem instanceof PhiNode ) return null;
    throw com.cliffc.aa.AA.unimpl(); // Break out another SESE split
  }

  // Move one escape set from the lower Split/Join to the upper.
  private Node combine_splits( GVNGCM gvn, MemSplitNode head ) {
    MemSplitNode msp = msp();
    MemJoinNode mjn = (MemJoinNode)msp.mem();
    if( _defs._len==1 ) return null; // Nothing to move
    if( true )
      // TODO: Fails right now because types get OOO when removing a Split/Join

      // TODO: Perhaps: upon moving a SESE region into the Split/Join,
      // immediately the Split types the 'other' aliases as "use" (ISUSED),
      // i.e. low as possible.  Later optimizations that lift these nodes (such
      // as when the Split/Join optimizes away) then only lifts types.
      return null;

    // Get the escaping set being moved.
    // Remove esc set from lower rollup and add to upper
    BitsAlias esc = msp._escs.pop();
    msp._escs.set(0,(BitsAlias)msp._escs.at(0).subtract(esc));
    int idx = head.add_alias(gvn,esc);
    assert idx!=0; // No partial overlaps; actually we could just legit bail here, no assert
    if( idx == mjn._defs._len ) // Add edge Join->Split as needed
      gvn.add_def(mjn,gvn.xform(new MProjNode(head,idx))); // Add a new MProj from MemSplit
    // Move SESE region from lower Split/Join to upper Split/Join
    ProjNode prj = ProjNode.proj(msp,msp._escs._len);
    gvn.subsume(prj,mjn.in(idx));
    gvn.set_def_reg(mjn,idx,in(_defs._len-1));
    gvn.remove_reg(this,_defs._len-1);

    // Moving this can *lower* the upper Join type, if an allocation moves up.
    Type tt = mjn.value(gvn);
    gvn.setype(mjn,tt);
    gvn.setype(msp,msp.value(gvn));
    for( Node use : msp._uses )
      gvn.setype(use,tt);

    return this;
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
    TypeObj[] pubs = new TypeObj[Env.DEFMEM._defs._len];
    TypeObj[] prvs = new TypeObj[Env.DEFMEM._defs._len];
    for( int alias=1, i; alias<Env.DEFMEM._defs._len; alias++ ) {
      if( escs.at(0).test_recur(alias) ) { // In some RHS set
        for( i=1; i<_defs._len; i++ )
          if( escs.at(i).test_recur(alias) )
            break;
      } else i=0;                     // In the base memory
      if( alias == 1 || Env.DEFMEM.in(alias) != null ) { // Check never-made aliases
        pubs[alias] = mems[i].at   (alias); // Merge alias
        prvs[alias] = mems[i].atprv(alias); // Merge alias
      }
    }
    return TypeMem.make0(pubs,prvs);
  }
  @Override public boolean basic_liveness() { return false; }

  // Move the given SESE region just ahead of the split into the join/split
  // area.  The head node has the escape-set.
  MemJoinNode add_alias_above( GVNGCM gvn, Node head ) {
    MemSplitNode msp = msp();
    Node base = msp.mem();                  // Base of SESE region
    assert base.check_solo_mem_writer(msp); // msp is only memory writer after base
    assert head.in(1).check_solo_mem_writer(head);   // head is the 1 memory writer after head.in
    int idx = msp.add_alias(gvn,head.escapees(gvn)); // Add escape set, find index
    Node mprj;
    if( idx == _defs._len ) {         // Escape set added at the end
      add_def(mprj = gvn.xform(new MProjNode(msp,idx))); // Add a new MProj from MemSplit
      mprj._live=_live;
    } else {
      assert idx!=0;     // No partial overlap; all escape sets are independent
      mprj = ProjNode.proj(msp,idx); // Find match MProj
    }
    // Resort edges to move SESE region inside
    mprj.keep();  base.keep();
    gvn.set_def_reg(msp,1,head.in(1)); // Move Split->base edge to Split->head.in(1)
    gvn.replace(mprj,base);            // Move split mprj users to base
    gvn.set_def_reg(head,1,mprj);      // Move head->head.in(1) to head->MProj
    mprj.unhook();   base.unhook();
    // Moving things inside the Split/Join region might let types get
    // out-of-order; the Split might be able to lift and be stale, while the
    // moved body is on the 'wrong side' of the stale Split.  Update the Split
    // and following MProjNodes immediately.
    Ary<Node> work = new Ary<>(new Node[]{msp});
    while( !work.isEmpty() ) {
      Node n = work.pop();
      assert n.is_mem();
      Type t0 = gvn.type(n);
      Type t1 = n.value(gvn);
      if( t0==t1 ) continue;
      gvn.setype(n,t1);
      if( n == this ) continue;
      for( Node use : n._uses ) if( use.is_mem() ) work.add(use);
    }
    // Update live same way
    base._live = base.live(gvn);
    if( base != head ) head._live = head.live(gvn);
    mprj._live = mprj.live(gvn);
    msp ._live = msp .live(gvn);
    return this;
  }

  // Move the given SESE region just behind of the join into the join/split
  // area.  The head node has the escape-set.
  void add_alias_below( GVNGCM gvn, Node head, Node base ) {
    assert head.is_mem() && base.is_mem();
    MemSplitNode msp = msp();
    int idx = msp.add_alias(gvn,head.escapees(gvn)), bidx; // Add escape set, find index
    if( idx == _defs._len ) {         // Escape set added at the end
      gvn.add_def(this,gvn.xform(new MProjNode(msp,idx)));
    } else {                    // Inserted into prior region
      assert idx!=0;     // No partial overlap; all escape sets are independent
    }
    // Reset edges to move SESE region inside
    Node mspj = in(idx);
    keep();
    gvn.set_def_reg(head,1,in(idx));
    gvn.replace(base,this);
    gvn.set_def_reg(unhook(),idx,base);
    // Move any accidental refs to DefMem back to base
    int didx = Env.DEFMEM._defs.find(this);
    if( didx != -1 ) gvn.set_def_reg(Env.DEFMEM,didx,base);
    // We just lost the off-alias updates.
    // Forward-flow new values.
    // Reverse-flow new lives.
    if( base==head ) gvn.revalive(mspj,head);
    else if( base.in(0)==head ) throw com.cliffc.aa.AA.unimpl(); //gvn.revalive(head,base);
    else gvn.revalive(mspj,head,base.in(0),base);
  }

  // Find a compatible alias edge, including base memory if nothing overlaps.
  // Return null for any partial overlaps.
  Node can_bypass( BitsAlias esc ) {
    Ary<BitsAlias> escs = msp()._escs;
    if( escs.at(0).join(esc) == BitsAlias.EMPTY ) // No overlap with any other alias set
      return msp().mem();          // Can completely bypass
    // Overlaps with at least 1
    for( int i=1; i<escs._len; i++ )
      if( esc.isa(escs.at(i)) ) // Fully contained with alias set 'i'?
        return in(i);           // Can use this memory
    return null;                // Not fully contained within any 1 alias set
  }
  // Modifies all of memory
  @Override BitsAlias escapees( GVNGCM gvn) { return BitsAlias.FULL; }
}
