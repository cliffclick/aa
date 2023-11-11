package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.MEM_IDX;
import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.Env.GVN;

// Join a split set of aliases from a SESE region, split by an earlier MemSplit.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemJoinNode extends Node {

  public MemJoinNode( MProjNode mprj ) { super(OP_JOIN,mprj);  assert mprj.in(0) instanceof MemSplitNode;  }

  MemSplitNode msp() {  // The MemSplit
    Node n = in(0).in(0);
    return n instanceof MemSplitNode ? (MemSplitNode)n : null;
  }
  @Override public boolean is_mem() { return true; }

  @Override public Node ideal_reduce() {
    MemSplitNode msp = msp();
    // If the split count is lower than 2, then the split serves no purpose
    if( _defs._len == 2 && val(1).isa(_val) ) {
      msp._is_copy=true;
      GVNGCM.retype_mem(null,msp(),in(1), false);
      for( Node use : msp()._uses ) GVN.add_reduce(use);
      return in(1);             // Just become the last split
    }

    // If some Split/Join path clears out, remove the (useless) split.
    for( int i=1; i<_defs._len; i++ )
      if( in(i) instanceof MProjNode && in(i).in(0)==msp && in(i)._uses._len==1 ) {
        in(0).xval();        // Update the default type
        msp.remove_alias(i);
        GVN.add_dead(in(i));
        return remove(i);
      }

    return null;
  }

  @Override public Node ideal_mono() {
    // If the Split memory has an obvious SESE region, move it into the Split
    MemSplitNode msp = msp();
    if( msp==null ) return null; // During cleanout of dead code
    Node mem = msp.mem();
    if( mem.check_solo_mem_writer(msp) ) { // Split is only memory writer after mem
      Node head = find_sese_head(mem);                       // Find head of SESE region
      if( head instanceof MemSplitNode )                     // Back to back split/join combo
        return combine_splits((MemSplitNode)head);
      if( head != null && head.in(1).check_solo_mem_writer(head) ) // Head is the only writer after the above-head
        // Move from Split.mem() to head inside the split/join area
        return add_alias_above(head);
    }
    return null;
  }


  static Node find_sese_head(Node mem) {
    if( mem instanceof MemJoinNode mjn ) return mjn.msp(); // Merge Split with prior Join
    if( mem instanceof StoreNode ) return mem;   // Move Store into Split/Join
    //if( mem instanceof MemPrimNode.LValueWrite ) return mem; // Array store
    if( mem instanceof MProjNode ) {
      Node head = mem.in(0);
      if( head instanceof CallNode ) return null; // Do not swallow a Call/CallEpi into a Split/Join
      if( head instanceof CallEpiNode ) return null; // Do not swallow a Call/CallEpi into a Split/Join
      if( head instanceof MemSplitNode ) return null; // TODO: Handle back-to-back split/join/split/join
      throw TODO(); // Break out another SESE split
    }
    if( mem instanceof ParmNode ) return null;
    if( mem instanceof PhiNode ) return null;
    if( mem instanceof ConNode ) return null;
    throw TODO(); // Break out another SESE split
  }

  // Move one escape set from the lower Split/Join to the upper.
  private Node combine_splits( MemSplitNode head ) {
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
    msp._escs.set(0,msp._escs.at(0).subtract(esc));
    int idx = head.add_alias(esc);
    assert idx!=0; // No partial overlaps; actually we could just legit bail here, no assert
    if( idx == mjn._defs._len ) // Add edge Join->Split as needed
      mjn.add_def(GVN.xform(new MProjNode(head,idx))); // Add a new MProj from MemSplit
    // Move SESE region from lower Split/Join to upper Split/Join
    ProjNode prj = ProjNode.proj(msp,msp._escs._len);
    prj.subsume(mjn.in(idx));
    mjn.set_def(idx,in(_defs._len-1));
    remove(_defs._len-1);

    // Moving this can *lower* the upper Join type, if an allocation moves up.
    Type tt = mjn.xval();
    msp.xval();
    for( Node use : msp._uses )
      use._val = tt;

    return this;
  }

  @Override public Type value() {
    MemSplitNode msp = msp();
    if( msp==null ) return TypeMem.ANYMEM;

    // "Shortcut" is all memories are the same (or any/all)
    boolean diff=false;
    TypeMem[] mems = new TypeMem[_defs._len];
    for( int i=0; i<_defs._len; i++ ) {
      Type t = val(i);
      if( t == Type.ANY ) t = TypeMem.ANYMEM;
      if( t == Type.ALL ) t = TypeMem.ALLMEM;
      if( !(t instanceof TypeMem) ) return t.oob(TypeMem.ALLMEM);
      mems[i] = (TypeMem)t;
      if( i>0 && !diff ) diff = mems[i]!=mems[0];
    }
    if( !diff ) return mems[0]; // All memories the same

    // Simply MEET.
    Type t = Type.ANY;
    for( TypeMem tmem : mems )
      t = t.meet(tmem);
    return t;
  }
  @Override public Type live_use( int i ) { return _live; }

  @Override public boolean has_tvar() { return false; }

  // Move the given SESE region just ahead of the split into the join/split
  // area.  The head node has the escape-set.
  MemJoinNode add_alias_above( Node head ) {
    MemSplitNode msp = msp();
    Node base = msp.mem();                  // Base of SESE region
    assert base.check_solo_mem_writer(msp); // msp is only memory writer after base
    assert head.in(1).check_solo_mem_writer(head);   // head is the 1 memory writer after head.in

    //int idx = msp.add_alias(head.escapees()); // Add escape set, find index
    //Node mprj;
    //if( idx == _defs._len ) {         // Escape set added at the end
    //  add_def(mprj = GVN.init(new MProjNode(msp,idx))); // Add a new MProj from MemSplit
    //} else {
    //  assert idx!=0;     // No partial overlap; all escape sets are independent
    //  mprj = ProjNode.proj(msp,idx); // Find match MProj
    //}
    //// Resort edges to move SESE region inside
    //msp.set_def(1,head.in(1)); // Move Split->base edge to Split->head.in(1)
    //mprj.insert(base);         // Move split mprj users to base
    //head.set_def(1,mprj);      // Move head->head.in(1) to head->MProj
    //// Must retype, since split memory
    //GVN.revalive(head,msp,mprj,base);
    //return this;
    throw TODO();
  }

  // Move the given SESE region just behind of the join into the join/split
  // area.  The head node has the escape-set.
  void add_alias_below( Node head, BitsAlias head1_escs, Node base ) {
    assert head.is_mem() && base.is_mem();
    GVN.add_unuse(this);
    MemSplitNode msp = msp();
    int idx = msp.add_alias(head1_escs); // Add escape set, find index
    Node mspj;
    if( idx == _defs._len ) {         // Escape set added at the end
      add_def(mspj = GVN.init(new MProjNode(msp,idx)));
    } else {             // Inserted into prior region
      mspj = in(idx);
      assert idx!=0;     // No partial overlap; all escape sets are independent
    }
    // Reset edges to move SESE region inside
    head.set_def(MEM_IDX,in(idx));
    base.insert(this);
    set_def(idx,base);
  }

  MemJoinNode add_alias_below_new(Node nnn, Node old ) {
    //add_alias_below(GVN.add_work_new(nnn),nnn.escapees(),nnn);
    //nnn.xval();  xval();        // Force update, since not locally monotonic
    //GVN.add_flow_defs(this);
    //assert Env.START.more_work(true)==0;
    //return this;
    throw TODO();
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
  //@Override BitsAlias escapees() { return BitsAlias.FULL; }
}
