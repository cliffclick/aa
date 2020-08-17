package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;

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
      _escs.at(i).toString(sb).p(',');
    return sb.unchar().p(')').toString();
  }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(byte opt_mode) {
    Type t = mem()._val;
    if( !(t instanceof TypeMem) ) return t.oob();
    // Normal type is for an MProj of the input memory, one per alias class
    Type[] ts = TypeAry.get(_escs._len);
    Arrays.fill(ts,t);
    return TypeTuple.make(ts);
  }
  @Override public boolean basic_liveness() { return false; }

  // Find the escape set this esc set belongs to, or make a new one.
  int add_alias( GVNGCM gvn, BitsAlias esc ) {
    BitsAlias all = _escs.at(0);   // Summary of Right Hand Side(s) escapes
    if( all.join(esc) == BitsAlias.EMPTY ) { // No overlap
      _escs.set(0,all.meet(esc));  // Update summary
      _escs.add(esc);              // Add escape set
      xval(gvn._opt_mode);         // Expand tuple result
      return _escs._len-1;
    }
    for( int i=1; i<_escs._len; i++ )
      if( esc.isa(_escs.at(i)) )
        return i;               // Found exact alias slice
    return 0;                   // No match, partial overlap
  }
  void remove_alias( GVNGCM gvn, int idx ) {
    // Remove (non-overlapping) bits from the rollup
    _escs.set(0,(BitsAlias)_escs.at(0).subtract(_escs.at(idx)));
    _escs.remove(idx);          // Remove the escape set
    TypeTuple tt = (TypeTuple)xval(gvn._opt_mode); // Reduce tuple result
    // Renumber all trailing projections to match
    for( Node use : _uses ) {
      MProjNode mprj = (MProjNode)use;
      if( mprj._idx > idx ) {
        gvn.unreg(mprj);
        mprj._idx--;
        gvn.rereg(mprj,tt.at(mprj._idx));
      }
    }
  }

  // A function body was cloned and all aliases split.  The 'this' Split takes
  // the first child and the clone takes the 2nd child.
  void split_alias( Node copy, BitSet aliases, GVNGCM gvn ) {
    gvn.add_work(this);
    MemSplitNode cmsp = (MemSplitNode)copy;
    for( int alias = aliases.nextSetBit(0); alias != -1; alias = aliases.nextSetBit(alias + 1)) {
      int[] kid0_aliases = BitsAlias.get_kids(alias);
      int newalias1 = kid0_aliases[1];
      int newalias2 = kid0_aliases[2];
      cmsp._update(alias,newalias1);
      this._update(alias,newalias2);
      gvn.add_work(join());
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
  static Node insert_split(GVNGCM gvn, Node tail1, Node head1, Node tail2, Node head2) {
    assert tail1.is_mem() && head1.is_mem() && tail2.is_mem() && head2.is_mem();
    BitsAlias head1_escs = head1.escapees();
    BitsAlias head2_escs = head2.escapees();
    assert check_split(gvn,head1,head1_escs);
    // Insert empty split/join above head2
    MemSplitNode msp = gvn.xform(new MemSplitNode(head2.in(1))).keep();
    MProjNode mprj = (MProjNode)gvn.xform(new MProjNode(msp,0));
    MemJoinNode mjn = (MemJoinNode)gvn.xform(new MemJoinNode(mprj));
    gvn.set_def_reg(head2,1,mjn);
    msp.unhook();
    mjn._live = tail1._live;
    // Pull the SESE regions in parallel from below
    mjn.add_alias_below(gvn,head2,head2_escs,tail2);
    mjn.add_alias_below(gvn,head1,head1_escs,tail1);
    gvn.revalive(msp,mprj,mjn);
    return head1;
  }
  static boolean check_split(GVNGCM gvn, Node head1, BitsAlias head1_escs) {
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
  @Override @NotNull public MemSplitNode copy( boolean copy_edges, GVNGCM gvn) {
    MemSplitNode nnn = (MemSplitNode)super.copy(copy_edges, gvn);
    nnn._escs = _escs.deepCopy();
    return nnn;
  }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    if( _uses._len==1 && _keep==0 ) return mem(); // Single user
    return null;
  }
    // Modifies all of memory - just does it in parts
  @Override BitsAlias escapees() { return BitsAlias.FULL; }
}
