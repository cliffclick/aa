package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeRPC;

import static com.cliffc.aa.AA.unimpl;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final Parse _badgc;
  final Type _t;                // Just a flag to signify scalar vs memory vs object
  PhiNode( byte op, Type t, Parse badgc, Node... vals ) {
    super(op,vals);
    _t = t;
    _badgc = badgc;
    if( t instanceof TypeMem || t instanceof TypeRPC ) _tvar=null;  // No HM for memory
  }
  public PhiNode( Type t, Parse badgc, Node... vals ) { this(OP_PHI,t,badgc,vals); }
  @Override public boolean is_mem() { return _t==TypeMem.ALLMEM; }
  @Override public int hashCode() { return super.hashCode()+_t.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PhiNode phi) ) return false;
    return _t==phi._t;
  }
  @Override void walk_reset0() {
    assert is_prim();
    while( len()>1 && !in(len()-1).is_prim() )
      pop(); // Kill wired primitive inputs
  }

  @Override public Node ideal_reduce() {
    if( in(0)==null ) return null; // Mid-construction
    if( val(0) == Type.XCTRL ) return null;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( r._val == Type.XCTRL ) return null; // All dead, c-prop will fold up
    if( r instanceof FunNode fun ) {
      if( fun.has_unknown_callers() ) return null; // Still finding incoming edges
      if( fun.noinline() )  return null; // Do not start peeling apart parameters to a no-inline function
    }
    // If only 1 unique live input, return that
    Node live=null;
    for( int i=1; i<_defs._len; i++ ) {
      if( r.val(i)==Type.XCTRL ) continue; // Ignore dead path
      Node n = in(i);
      if( n==this || n==live ) continue; // Ignore self or duplicates
      if( live==null ) live = n;         // Found unique live input
      else live=this;                    // Found 2nd live input, no collapse
    }
    if( live != this ) return live; // Single unique input

    return null;
  }
  @Override public Type value() {
    if( in(0)==null ) return Type.ALL; // Conservative, mid-construction
    Type ctl = val(0);
    if( ctl != Type.CTRL ) return ctl.oob();
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ )
      if( r.val(i)!=Type.XCTRL && r.val(i)!=Type.ANY ) // Only meet alive paths
        t = t.meet(val(i));
    return t;
  }

  // Yes for e.g. ints, flts, memptrs, funptrs.  A Phi corresponds to the
  // merging HM value in the core AA If.
  @Override public boolean has_tvar() { return !(_t instanceof TypeMem || _t instanceof TypeRPC); }
  
  // All inputs unify
  @Override public boolean unify( boolean test ) {
    if( !(in(0) instanceof RegionNode r) ) return false; // Dying
    if( _tvar==null ) return false; // Memory not part of HM
    boolean progress = false;
    for( int i=1; i<_defs._len; i++ ) {
      if( r.val(i)!=Type.XCTRL && r.val(i)!=Type.ANY ) { // Only unify alive paths
        progress |= tvar().unify(tvar(i),test);
        if( progress && test ) return true; // Fast cutout
      }
    }
    return progress;
  }

  //@Override BitsAlias escapees() { return BitsAlias.FULL; }
  @Override public Type live_use(Node def ) {
    Node r = in(0);
    if( r==def ) return Type.ALL;
    if( r!=null ) {
      if( r.len() != len() ) return _live;
      // The same def can appear on several inputs; check them all.
      int i; for( i=1; i<_defs._len; i++ )
        if( in(i)==def && !r.val(i).above_center() )
          break;                           // This input is live
      if( i==_defs._len ) return Type.ANY; // All matching defs are not live on any path
    }
    // Def is alive (on some path)
    return _live;
  }

  @Override public ErrMsg err( boolean fast ) {
    //if( _val.contains(TypeNil.SCALAR) ||
    //    _val.contains(TypeNil.NSCALR) ) // Cannot have code that deals with unknown-GC-state
    //  return ErrMsg.badGC(_badgc);
    //return null;
    throw unimpl();
  }
}
