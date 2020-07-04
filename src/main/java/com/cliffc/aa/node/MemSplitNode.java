package com.cliffc.aa.node;

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
  Ary<BitsAlias> _escs = new Ary<>(new BitsAlias[]{BitsAlias.EMPTY});
  public MemSplitNode( Node mem ) { super(OP_SPLIT,null,mem); }
  Node mem() { return in(1); }
  MemJoinNode join() {
    Node prj = ProjNode.proj(this,0);
    if( prj==null ) return null;
    return (MemJoinNode)prj._uses.at(0);
  }

  @Override String str() {
    SB sb = new SB().p('(');
    sb.p("base,");
    for( int i=1; i<_escs._len; i++ )
      _escs.at(i).toString(sb).p(',');
    return sb.unchar().p(')').toString();
  }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(mem());
    if( !(t instanceof TypeMem) ) return t.oob();
    // Normal type is for an MProj of the input memory, one per alias class
    Type[] ts = TypeAry.get(_escs._len);
    Arrays.fill(ts,t);
    return TypeTuple.make(ts);
  }
  @Override public boolean basic_liveness() { return false; }

  // Find the escape set this esc set belongs to, or make a new one.
  int add_alias( GVNGCM gvn, BitsAlias esc ) {
    BitsAlias all = _escs.at(0); // Summary of Right Hand Side(s) escapes
    if( esc.join(all)==BitsAlias.EMPTY ) { // No overlap
      _escs.set(0,esc.meet(all));          // Update summary
      _escs.add(esc);                      // Add escape set
      gvn.setype(this,value(gvn));         // Expand tuple result
      return _escs._len-1;
    }
    for( int i=1; i<_escs._len; i++ )
      if( esc.isa(_escs.at(i)) )
        return i;               // Found exact alias slice
    return 0;                   // No match, partial overlap
  }
  void remove_alias( GVNGCM gvn, int idx ) {
    _escs.remove(idx);
    // Recompute the roll-up.  TODO: since all are disjoint, a version of bit 'subtract' works
    BitsAlias escs = BitsAlias.EMPTY;
    for( int i=1; i<_escs._len; i++ )
      escs = escs.meet(_escs.at(i));
    _escs.set(0,escs);
    TypeTuple tt = (TypeTuple)value(gvn);
    gvn.setype(this,tt);        // Reduce tuple result
    // Renumber all trailing projections to match
    for( Node use : _uses ) {
      MProjNode mprj = (MProjNode)use;
      if( mprj._idx > idx ) {
        gvn.unreg(mprj);
        mprj._idx--;
        gvn.rereg(mprj,tt.at(0));
      }
    }
  }

  // A function body was cloned and all aliases split.  The 'this' Split takes
  // the first child and the clone takes the 2nd child.
  void split_alias( Node copy, BitSet aliases, GVNGCM gvn ) {
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
    if( esc0.test_recur(oldalias) ) {
      _escs.set(0, esc0.clear(oldalias).set(newalias));
      for( int i=1; i<_escs._len; i++ ) {
        BitsAlias esc = _escs.at(i);
        if( esc.test_recur(oldalias) ) {
          _escs.set(i, esc.clear(oldalias).set(newalias));
          break;
        }
      }
    }
  }

  //@SuppressWarnings("unchecked")
  @Override @NotNull public MemSplitNode copy( boolean copy_edges, GVNGCM gvn) {
    MemSplitNode nnn = (MemSplitNode)super.copy(copy_edges, gvn);
    nnn._escs = _escs.deepCopy();
    return nnn;
  }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    return _uses._len==1 && _keep==0 ? mem() : null;
  }
    // Modifies all of memory - just does it in parts
  @Override BitsAlias escapees(GVNGCM gvn) { return BitsAlias.FULL; }
}
