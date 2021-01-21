package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TMem;
import com.cliffc.aa.tvar.TVDead;
import com.cliffc.aa.tvar.TVar;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;

// TODO: Parse12 gen test, seeing many back-to-back identical split/join.

// Split a set of aliases into a SESE region, to be joined by a later MemJoin.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemSplitNode extends Node {
  Ary<BitsAlias> _escs = new Ary<>(new BitsAlias[]{new BitsAlias()});
  public MemSplitNode( Node mem ) { super(OP_SPLIT,null,mem); }
  Node mem() { return in(1); }
  public MemJoinNode join() {

    Node prj = ProjNode.proj(this,0);
    if( prj==null ) return null;
    return (MemJoinNode)prj._uses.at(0);
  }

  @Override public boolean is_mem() { return true; }
  @Override String str() {
    SB sb = new SB();
    sb.p('(').p("base,");
    for( int i=1; i<_escs._len; i++ )
      _escs.at(i).str(sb).p(',');
    return sb.unchar().p(')').toString();
  }
  @Override public Node ideal(GVNGCM gvn, int level) { throw com.cliffc.aa.AA.unimpl(); }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type t = mem().val();
    if( !(t instanceof TypeMem) ) return t.oob();
    // Normal type is for an MProj of the input memory, one per alias class
    Type[] ts = Types.get(_escs._len);
    Arrays.fill(ts,t);
    return TypeTuple.make(ts);
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }

  @Override public boolean unify( boolean test ) {
    TVar tvar = tvar();
    if( tvar instanceof TVDead ) return false; // Not gonna be a TMem
    if( !(tvar instanceof TMem) )
      return test || tvar.unify(new TMem(this),test);
    // Input should be a TMem also
    TVar dmem = mem().tvar();
    if( dmem instanceof TVDead ) return false; // Not gonna be a TMem
    if( !(dmem instanceof TMem) )
      return test || dmem.unify(new TMem(this),test);
    return tvar.unify(dmem,test);
  }

  // Find index for alias
  int find_alias_index( int alias ) {
    if( !_escs.at(0).test(alias) ) return 0; // Not in any set, so base
    for( int i=1; i<_escs._len; i++ )
      if( _escs.at(i).test(alias) )
        return i;
    throw com.cliffc.aa.AA.unimpl(); // Should be found
  }

  // Find the escape set this esc set belongs to, or make a new one.
  int add_alias( BitsAlias esc ) {
    assert !esc.is_empty();
    BitsAlias all = _escs.at(0);   // Summary of Right Hand Side(s) escapes
    if( all.join(esc) == BitsAlias.EMPTY ) { // No overlap
      _escs.set(0,all.meet(esc));  // Update summary
      _escs.add(esc);              // Add escape set
      xval();                      // Expand tuple result
      return _escs._len-1;
    }
    for( int i=1; i<_escs._len; i++ )
      if( esc.isa(_escs.at(i)) )
        return i;               // Found exact alias slice
    return 0;                   // No match, partial overlap
  }
  void remove_alias( int idx ) {
    // Remove (non-overlapping) bits from the rollup
    _escs.set(0,(BitsAlias)_escs.at(0).subtract(_escs.at(idx)));
    _escs.remove(idx);          // Remove the escape set
    xval();                     // Reduce tuple result
    // Renumber all trailing projections to match
    for( Node use : _uses ) {
      MProjNode mprj = (MProjNode)use;
      if( mprj._idx > idx )
        mprj.set_idx(mprj._idx-1);
    }
  }

  // A function body was cloned and all aliases split.  The 'this' Split takes
  // the first child and the clone takes the 2nd child.
  void split_alias( Node copy, BitSet aliases ) {
    MemSplitNode cmsp = (MemSplitNode)copy;
    for( int alias = aliases.nextSetBit(0); alias != -1; alias = aliases.nextSetBit(alias + 1)) {
      int[] kid0_aliases = BitsAlias.get_kids(alias);
      int newalias1 = kid0_aliases[1];
      int newalias2 = kid0_aliases[2];
      cmsp._update(alias,newalias1);
      this._update(alias,newalias2);
    }
  }
  // Replace the old alias with the new child alias
  private void _update(int oldalias, int newalias) {
    BitsAlias esc0 = _escs.at(0);
    if( esc0.test(oldalias) ) {
      _escs.set(0, esc0.set(newalias));
      for( int i=1; i<_escs._len; i++ ) {
        BitsAlias esc = _escs.at(i);
        if( esc.test(oldalias) ) {
          _escs.set(i, esc.set(newalias));
          break;
        }
      }
    }
  }

  // Insert a Split/Join pair, moving the two stacked memory SESE regions
  // side-by-side.  If the SESE region is empty, the head & tail can be the
  // same, which is true for e.g. StoreNodes & MrgNodes.
  //      tail1->{SESE#1}->head1->tail2->{SESE#2}->head2
  // New/Mrg pairs are just the Mrg; the New is not part of the SESE region.
  // Call/CallEpi pairs are: MProj->{CallEpi}->Call.
  static Node insert_split(Node tail1, BitsAlias head1_escs, Node head1, Node tail2, Node head2) {
    assert tail1.is_mem() && head1.is_mem() && tail2.is_mem() && head2.is_mem();
    BitsAlias head2_escs = head2.escapees();
    assert check_split(head1,head1_escs);
    // Insert empty split/join above head2
    MemSplitNode msp = Env.GVN.init(new MemSplitNode(head2.in(1))).unkeep();
    MProjNode    mprj= Env.GVN.init(new MProjNode   (msp,0      )).unkeep();
    MemJoinNode  mjn = Env.GVN.init(new MemJoinNode (mprj       )).unkeep();
    head2.set_def(1,mjn);
    mjn._live = tail1._live;
    // Pull the SESE regions in parallel from below
    mjn.add_alias_below(head2,head2_escs,tail2);
    mjn.add_alias_below(head1,head1_escs,tail1);
    if( mprj.is_dead() ) Env.GVN.revalive(msp);
    else Env.GVN.revalive(msp,mprj,mjn);
    assert Env.START.more_flow(true)==0;
    return head1;
  }

  static boolean check_split( Node head1, BitsAlias head1_escs ) {
    Node tail2 = head1.in(1);
    // Must have only 1 mem-writer (this can fail if used by different control paths)
    if( !tail2.check_solo_mem_writer(head1) ) return false;
    // No alias overlaps
    if( head1_escs.overlaps(tail2.escapees()) ) return false;
    // TODO: This is too strong.
    // Cannot have any Loads following head1; because after the split
    // they will not see the effects of previous stores that also move
    // into the split.
    return (tail2._uses._len==1) ||
      (tail2._uses._len==2 && tail2._uses.find(Env.DEFMEM)!= -1 );
  }


  //@SuppressWarnings("unchecked")
  @Override @NotNull public MemSplitNode copy( boolean copy_edges) {
    MemSplitNode nnn = (MemSplitNode)super.copy(copy_edges);
    nnn._escs = _escs.deepCopy();
    return nnn;
  }
  @Override public Node is_copy(int idx) {
    if( _uses._len==1 && _keep==0 ) return mem(); // Single user
    return null;
  }
    // Modifies all of memory - just does it in parts
  @Override BitsAlias escapees() { return BitsAlias.FULL; }
}
