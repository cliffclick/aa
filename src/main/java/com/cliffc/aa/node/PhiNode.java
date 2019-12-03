package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;

import java.util.HashMap;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final Parse _badgc;
  private final BitsAlias _bits;
  private PhiNode( byte op, Parse badgc, Node... vals ) {
    super(op,vals);
    _badgc = badgc;
    _bits = BitsAlias.NZERO;
  }
  public PhiNode( Parse badgc, Node... vals ) { this(OP_PHI,badgc,vals); }
  // For ParmNodes
  PhiNode( byte op, Node fun, ConNode defalt, Parse badgc ) { this(op,badgc,fun,defalt); }

  @Override public Node ideal(GVNGCM gvn) {
    if( gvn.type(in(0)) == Type.XCTRL ) return null;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( gvn.type(r) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    if( r._defs.len() > 1 &&  r.in(1) == Env.ALL_CTRL ) return null;
    if( r instanceof FunNode && ((FunNode)r).noinline() )
      return null; // Do not start peeling apart parameters to a no-inline function
    // If only 1 unique live input, return that
    Node live=null;
    for( int i=1; i<_defs._len; i++ ) {
      if( gvn.type(r.in(i))==Type.XCTRL ) continue; // Ignore dead path
      if( in(i)==this || in(i)==live ) continue;    // Ignore self or duplicates
      if( live==null ) live = in(i);                // Found unique live input
      else live=this;           // Found 2nd live input, no collapse
    }
    if( live != this ) return live; // Single unique input

    // Phi of a MemMerge becomes a MemMerge of a Phi - increasing the precision
    // of memory edges.
    if( gvn.type(in(1)) instanceof TypeMem ) {
      Node rez = expand_memory(r,gvn);
      if( rez != null ) return rez;
    }

    return null;
  }

  // Phi of a MemMerge becomes a MemMerge of a Phi - increasing the precision
  // of memory edges.
  private Node expand_memory(RegionNode r, GVNGCM gvn) {
    // Profit heuristic: all MemMerges are stable after xform and at least one
    // exists and the Phi is the sole user, so the input MemMerge will die
    // after this xform.  This is an expanding xform: try not to expand dead
    // nodes.  Xform the inputs first, in case they just fold away.
    boolean has_mmem=false;
    for( int i=1; i<_defs._len; i++ ) {
      if( in(i)._uses._len==1 && in(i) instanceof MemMergeNode ) {
        gvn.xform_old(in(i));
        if( in(i)._uses._len==1 && in(i) instanceof MemMergeNode )
          has_mmem=true;
      }
    }
    if( !has_mmem ) return null;

    // Do the expansion.  First: make all the Phis
    HashMap<Integer,PhiNode> phis = new HashMap<>();
    phis.put(BitsAlias.ALL,new PhiNode(_badgc,r));
    for( int i=1; i<_defs._len; i++ )
      if( in(i) instanceof MemMergeNode ) {
        MemMergeNode xmem = (MemMergeNode)in(i);
        for( int j=0; j<xmem._defs._len; j++ ) {
          int alias = xmem.alias_at(j);
          PhiNode phi = phis.get(alias);
          if( phi==null ) phis.put(alias,new PhiNode(_badgc,r));
        }
      }
    // Now fill in all the phis, one by one, and plug into the giant MemMerge
    // at the end.
    MemMergeNode mmem = new MemMergeNode(null);
    for( int alias : phis.keySet() ) {
      PhiNode phi = phis.get(alias);
      for( int i=1; i<_defs._len; i++ ) {
        Node n = in(i), m=n;
        // Take the matching narrow slice for the alias, except for alias ALL
        // which can keep taking undistinguished memory.  The resulting memory
        // is {ALL-aliases} but currently only represented as ALL.
        if( n instanceof MemMergeNode )
          m = n = ((MemMergeNode)n).alias2node(alias);
        if( alias==BitsAlias.ALL ) {
          assert gvn.type(m) instanceof TypeMem;
        } else {
          if( gvn.type(m) instanceof TypeMem )
            m = gvn.xform(new ObjMergeNode(n,alias));
          assert gvn.type(m) instanceof TypeObj;
        }
        phi.add_def(m);
      }
      Node obj = gvn.xform(phi);
      if( alias==BitsAlias.ALL ) mmem.set_def(0,obj,gvn);
      else       mmem.create_alias_active(alias,obj,gvn);
    }
    return mmem;
  }


  @Override public Type value(GVNGCM gvn) {
    Type ctl = gvn.type(in(0));
    if( ctl != Type.CTRL ) return ctl.above_center() ? Type.ANY : Type.ALL;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.in(i))==Type.CTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    return t;                   // Limit to sane results
  }
  @Override public Type all_type() { return Type.ALL; }
  @Override public String err(GVNGCM gvn) {
    if( !(in(0) instanceof FunNode && ((FunNode)in(0))._name.equals("!") ) && // Specifically "!" takes a Scalar
        (gvn.type(this).contains(Type.SCALAR) ||
         gvn.type(this).contains(Type.NSCALR)) ) // Cannot have code that deals with unknown-GC-state
      return _badgc.errMsg("Cannot mix GC and non-GC types");
    return null;
  }
}
