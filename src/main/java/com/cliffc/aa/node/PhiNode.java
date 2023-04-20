package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final Parse _badgc;
  final Type _t;                // Just a flag to signify scalar vs memory vs object


  // If this is the merge of a value defined in an IF, the usage is correct in
  // each arm of the IF, but might not be correct afterwards.  Keep precision
  // in the IF arms, but fresh-unify afterwards.
  // Example:
  //    rez_is_4 = rand ? (x=2; x*x) : (x="abcd"; #x); // these two x's are not compatible
  //    ... here x is an [Err cannot unify 2 and "abcd"]...
  //final boolean _ifresh;        // Defined in an IF, use FRESH_UNIFY not UNIFY
  
  PhiNode( byte op, Type t, Parse badgc, Node... vals ) {
    super(op,vals);
    _t = t;
    _badgc = badgc;
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

  @Override public Node ideal_reduce() {
    if( in(0)==null ) return null; // Mid-construction
    if( val(0) == Type.XCTRL ) return null;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( r._val == Type.XCTRL ) return null; // All dead, c-prop will fold up
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
    if( ctl != Type.CTRL && ctl!= Type.ALL ) return _t.dual(); //ctl.oob();
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    Type t = _t.dual();
    for( int i=1; i<_defs._len; i++ ) {
      r.in(i).deps_add(this);
      if( r.val(i)!=Type.XCTRL && r.val(i)!=Type.ANY ) // Only meet alive paths
        t = t.meet(val(i));
    }
    return t;
  }
  @Override public Type live_use(Node def ) {
    Node r = in(0);
    if( r==def  ) return Type.ALL; // Self-loop, error
    if( r==null ) return _live;    // Mid-collapse, error, pass live thru
    if( r.len() != len() ) return _live; // Error, pass live thru
    // The same def can appear on several inputs; check them all.
    for( int i=1; i<_defs._len; i++ )
      if( in(i)==def && !r.val(i).above_center() ) {
        r.in(i).deps_add(def);
        return _live==Type.ALL && _t==TypeMem.ALLMEM ? _t : _live;         // This input is as live as i am
      }
    // If the control changes, recompute live
    for( int i=1; i<_defs._len; i++ ) if( in(i)==def )  r.in(i).deps_add(def);
    return Type.ANY;            // All matching defs are not live on any path
  }

  // Yes for e.g. ints, flts, memptrs, funptrs.  A Phi corresponds to the
  // merging HM value in the core AA If.
  @Override public boolean has_tvar() { return !(_t instanceof TypeMem || _t instanceof TypeRPC); }

  // All inputs unify
  @Override public boolean unify( boolean test ) {
    if( !(in(0) instanceof RegionNode r) ) return false; // Dying
    if( val(0) != Type.CTRL && val(0)!= Type.ALL ) return false; // Control is dead
    if( !has_tvar() ) return false; // Memory not part of HM
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

  @Override public ErrMsg err( boolean fast ) {
    // TODO:
    //if( _val.contains(TypeNil.SCALAR) ||
    //    _val.contains(TypeNil.NSCALR) ) // Cannot have code that deals with unknown-GC-state
    //  return ErrMsg.badGC(_badgc);

    // Cannot mix TFPs with and without displays, because we do not know if we
    // should early-bind or late-bind.
    boolean has_dsp=false, no_dsp=false;
    for( Node def : _defs )
      if( def._val instanceof TypeFunPtr tfp )
        if( tfp.has_dsp() ) has_dsp = true;
        else                 no_dsp = true;
    if( has_dsp && no_dsp )
      throw unimpl();
    
    return null;
  }
}
