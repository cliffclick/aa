package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;

import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.AA.CTL_IDX;

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
  
  public PhiNode( Type t, Parse badgc, Node... vals ) {
    super(vals);
    _t = t;
    _badgc = badgc;
  }
  @Override public String label() { return "Phi"; }
  @Override public boolean isMem() { return _t==TypeMem.ALLMEM; }
  @Override public int hashCode() { return super.hashCode()+_t.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PhiNode phi) ) return false;
    return _t==phi._t;
  }

  @Override public Node ideal_reduce() {
    if( isPrim() ) return null;
    if( in(0)==null ) return null; // Mid-construction
    if( val(0) == Type.XCTRL ) return null;
    RegionNode r = (RegionNode) in(0);
    assert r.len()==len();
    if( r._val == Type.XCTRL ) return null; // All dead, c-prop will fold up
    // If only 1 unique live input, return that
    Node live=null;
    for( int i=1; i<len(); i++ ) {
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
    assert r.len()==len();
    Type t = _t.dual();
    for( int i=1; i<len(); i++ ) {
      r.in(i).deps_add(this);
      if( r.val(i)!=Type.XCTRL && r.val(i)!=Type.ANY ) // Only meet alive paths
        t = t.meet(val(i));
    }
    return t;
  }
  @Override public Type live_use( int i ) {
    if( i == CTL_IDX  ) return Type.ALL; // Self-loop, error
    Node r = in(0);
    if( r == null ) return _live; // Mid-collapse, error, pass live thru
    if( r == Env.XCTRL ) return Type.ANY;
    if( r.len() != len() ) return _live; // Error, pass live thru
    // If the control changes, recompute live
    r.in(i).deps_add(in(i));
    if( r.val(i).above_center() )
      return Type.ANY;          // Not control alive
    return _live==Type.ALL && _t==TypeMem.ALLMEM ? _t : _live;         // This input is as live as i am
  }

  // Yes for e.g. ints, flts, memptrs, funptrs.  A Phi corresponds to the
  // merging HM value in the core AA If.
  @Override public boolean has_tvar() { return !isMem(); }
  @Override public TV3 _set_tvar() { return new TVLeaf(); }

  // All inputs unify
  @Override public boolean unify( boolean test ) {
    if( !(in(0) instanceof RegionNode r) ) return false; // Dying
    if( val(0) != Type.CTRL && val(0)!= Type.ALL ) return false; // Control is dead
    if( !has_tvar() ) return false; // Memory not part of HM
    boolean progress = false;
    for( int i=1; i<len(); i++ ) {
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
    for( Node def : defs() )
      if( def._val instanceof TypeFunPtr tfp )
        if( tfp.has_dsp() ) has_dsp = true;
        else                 no_dsp = true;
    if( has_dsp && no_dsp )
      throw TODO();
    
    return null;
  }
}
