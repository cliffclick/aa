package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.TNode;
import com.cliffc.aa.tvar.TMem;
import com.cliffc.aa.tvar.TVDead;
import com.cliffc.aa.tvar.TVar;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.Env.GVN;

// Join a split set of aliases from a SESE region, split by an earlier MemSplit.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemJoinNode extends Node {

  public MemJoinNode( MProjNode mprj ) { super(OP_JOIN,mprj); assert mprj.in(0) instanceof MemSplitNode; }

  MemSplitNode msp() { return (MemSplitNode)in(0).in(0); }  // The MemSplit
  @Override public boolean is_mem() { return true; }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If the split count is lower than 2, then the split serves no purpose
    if( _defs._len == 2 && val(1).isa(val()) && _keep==0 )
      return in(1);             // Just become the last split

    // If some Split/Join path clears out, remove the (useless) split.
    MemSplitNode msp = msp();
    for( int i=1; i<_defs._len; i++ )
      if( in(i) instanceof MProjNode && in(i).in(0)==msp && in(i)._uses._len==1 ) {
        in(0).xval();        // Update the default type
        msp.remove_alias(i);
        return remove(i);
      }

    // If the Split memory has an obvious SESE region, move it into the Split
    Node mem = msp.mem();
    if( !mem.is_prim() && mem.check_solo_mem_writer(msp) ) { // Split is only memory writer after mem
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
    if( mem instanceof MemJoinNode ) return ((MemJoinNode)mem).msp(); // Merge Split with prior Join
    if( mem instanceof StoreNode ) return mem;   // Move Store into Split/Join
    if( mem instanceof MemPrimNode.LValueWrite ) return mem; // Array store
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
    if( mem instanceof StartMemNode ) return null;
    if( mem instanceof ConNode ) return null;
    throw com.cliffc.aa.AA.unimpl(); // Break out another SESE split
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
    msp._escs.set(0,(BitsAlias)msp._escs.at(0).subtract(esc));
    int idx = head.add_alias(esc);
    assert idx!=0; // No partial overlaps; actually we could just legit bail here, no assert
    if( idx == mjn._defs._len ) // Add edge Join->Split as needed
      mjn.add_def(Env.GVN.xform(new MProjNode(head,idx))); // Add a new MProj from MemSplit
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

  @Override public Type value(GVNGCM.Mode opt_mode) {
    // Gather all memories
    boolean diff=false;
    TypeMem[] mems = new TypeMem[_defs._len];
    for( int i=0; i<_defs._len; i++ ) {
      Type t = val(i);
      if( !(t instanceof TypeMem) ) return t.oob(TypeMem.ALLMEM);
      mems[i] = (TypeMem)t;
      if( i>0 && !diff ) diff = mems[i]!=mems[0];
    }
    if( !diff ) return mems[0]; // All memories the same

    // Walk all aliases and take from matching escape set in the Split.  Since
    // nothing overlaps this is unambiguous.
    Ary<BitsAlias> escs = msp()._escs;
    TypeObj[] pubs = new TypeObj[Env.DEFMEM._defs._len];
    for( int alias=1, i; alias<Env.DEFMEM._defs._len; alias++ ) {
      if( escs.at(0).test_recur(alias) ) { // In some RHS set
        for( i=1; i<_defs._len; i++ )
          if( escs.at(i).test_recur(alias) )
            break;
      } else i=0;                     // In the base memory
      if( alias == 1 || Env.DEFMEM.in(alias) != null ) // Check never-made aliases
        pubs[alias] = mems[i].at(alias); // Merge alias
    }
    return TypeMem.make0(pubs);
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }

  // Unify alias-by-alias, except on the alias sets
  @Override public boolean unify( boolean test ) {
    // Self has to be a TMem
    TVar tvar = tvar();
    if( tvar instanceof TVDead ) return false; // Not gonna be a TMem
    if( !(tvar instanceof TMem) )
      return test || tvar.unify(new TMem(this),test);
    TMem tvarm = (TMem)tvar;

    // Inputs should be TMems also
    boolean progress = false;
    for( Node def : _defs ) {
      TVar dmem = def.tvar();
      if( dmem instanceof TVDead ) return progress; // Not gonna be a TMem
      if( !(dmem instanceof TMem) )
        progress |= dmem.unify(new TMem(def),test);
    }
    if( test && progress ) return progress;

    // Base has to be a TMem
    TMem tbasem = (TMem)tvar(0);
    // Unify aliases outside of the esc set from the base
    Ary<BitsAlias> escs = msp()._escs;
    progress |= tvarm.unify_mem(escs.at(0),tbasem,test);
    // If we widen the TMem here, all inputs will widen as well
    //if( !test && progress )
    //  for( Node def : _defs )
    //    TNode.add_work(def);

    //// Unify inputs alias by alias
    //for( int i=1; i<_defs._len; i++ )
    //  progress |= tvarm.unify_alias(escs.at(i),(TMem)tvar(i),test);
    //return progress;
    throw com.cliffc.aa.AA.unimpl();
  }

  // Move the given SESE region just ahead of the split into the join/split
  // area.  The head node has the escape-set.
  MemJoinNode add_alias_above( Node head ) {
    MemSplitNode msp = msp();
    Node base = msp.mem();                  // Base of SESE region
    assert base.check_solo_mem_writer(msp); // msp is only memory writer after base
    assert head.in(1).check_solo_mem_writer(head);   // head is the 1 memory writer after head.in
    int idx = msp.add_alias(head.escapees()); // Add escape set, find index
    Node mprj;
    if( idx == _defs._len ) {         // Escape set added at the end
      add_def(mprj = GVN.xform(new MProjNode(msp,idx))); // Add a new MProj from MemSplit
      mprj._live=_live;
    } else {
      assert idx!=0;     // No partial overlap; all escape sets are independent
      mprj = ProjNode.proj(msp,idx); // Find match MProj
    }
    // Resort edges to move SESE region inside
    mprj.keep();  base.keep();
    msp.set_def(1,head.in(1)); // Move Split->base edge to Split->head.in(1)
    mprj.insert(base);         // Move split mprj users to base
    head.set_def(1,mprj);      // Move head->head.in(1) to head->MProj
    mprj.unkeep();   base.unkeep();
    // Moving things inside the Split/Join region might let types get
    // out-of-order; the Split might be able to lift and be stale, while the
    // moved body is on the 'wrong side' of the stale Split.  Update the Split
    // and following MProjNodes immediately.
    Ary<Node> work = new Ary<>(new Node[]{msp});
    while( !work.isEmpty() ) {
      Node n = work.pop();
      assert n.is_mem();
      Type t0 = n.val();
      Type t1 = n.value(GVN._opt_mode);
      if( t0==t1 ) continue;
      n._val = t1;
      if( n == this ) continue;
      for( Node use : n._uses ) if( use.is_mem() ) work.add(use);
    }
    // Update live same way
    base.xliv(GVN._opt_mode);
    if( base != head ) head.xliv(GVN._opt_mode);
    mprj.xliv(GVN._opt_mode);
    msp .xliv(GVN._opt_mode);
    // TODO: Re-establish H-M invariants
    return this;
  }

  // Move the given SESE region just behind of the join into the join/split
  // area.  The head node has the escape-set.
  void add_alias_below( Node head, BitsAlias head1_escs, Node base ) {
    assert head.is_mem() && base.is_mem();
    MemSplitNode msp = msp();
    int idx = msp.add_alias(head1_escs), bidx; // Add escape set, find index
    if( idx == _defs._len ) {         // Escape set added at the end
      add_def(Env.GVN.xform(new MProjNode(msp,idx)));
    } else {             // Inserted into prior region
      assert idx!=0;     // No partial overlap; all escape sets are independent
    }
    // Reset edges to move SESE region inside
    Node mspj = in(idx);
    keep();
    head.set_def(1,in(idx));
    base.insert(this);
    unkeep().set_def(idx,base);
    // Move any accidental refs to DefMem back to base
    int didx = Env.DEFMEM._defs.find(this);
    if( didx != -1 ) Env.DEFMEM.set_def(didx,base);
    // We just lost the off-alias updates.
    // Forward-flow new values.
    // Reverse-flow new lives.
    if( base==head ) Env.GVN.revalive(mspj,head);
    else if( base.in(0)==head ) throw com.cliffc.aa.AA.unimpl(); //gvn.revalive(head,base);
    else Env.GVN.revalive(mspj,head,base.in(0),base);
  }

  MemJoinNode add_alias_below_new(Node nnn, Node old ) {
    old.keep();                 // Called from inside old.ideal(), must keep alive until exit
    Node nnn2 = GVN.xform(nnn.keep()).unkeep();
    add_alias_below(nnn2,nnn2.escapees(),nnn2);
    old.unkeep();               // Alive, but keep==0
    nnn2.xval();
    xval();
    //gvn.add_work_defs(this);
    //return this;
    throw com.cliffc.aa.AA.unimpl();
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
  @Override BitsAlias escapees() { return BitsAlias.FULL; }
}
