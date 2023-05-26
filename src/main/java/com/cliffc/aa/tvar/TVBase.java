package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.PrimNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

public class TVBase extends TVExpanding {
  public Type _t;  
  private TVBase( Type t ) {
    assert t!=Type.ALL;
    _t = t;
  }
  public static TV3 make( Type t) {
    return t==Type.ALL ? new TVLeaf() : new TVBase(t);
  }

  @Override boolean can_progress() {
    if( _t instanceof TypeInt ) return _t!=TypeInt.INT64;
    if( _t instanceof TypeFlt ) return _t!=TypeFlt.FLT64;
    throw unimpl();
  }
  
  @Override int eidx() {
    if( _t instanceof TypeInt ) return TVErr.XINT;
    if( _t instanceof TypeFlt ) return TVErr.XFLT;
    throw unimpl(); // 
  }

  @Override TV3 strip_nil() {
    _t = _t.join(TypeNil.NSCALR);
    _may_nil = false;
    return this;
  }

  // Convert the leader nil into a base+NIL, widened if the leader is not a
  // copy.
  @Override TV3 find_nil( ) {
    Type t = _t.meet(TypeNil.NIL);
    if( t==_t && _may_nil )
      return this;
    // Need a new base, because may_nil changes
    TVBase b = new TVBase(t);
    b.add_may_nil(false);
    b.widen(_widen,false);
    return b;
  }

  public TVPtr clz() {
    if( _t instanceof TypeInt ) return (TVPtr)PrimNode.PINT.tvar();
    if( _t instanceof TypeFlt ) return (TVPtr)PrimNode.PFLT.tvar();
    throw unimpl();
  }
  
  // -------------------------------------------------------------
  @Override public void _union_impl(TV3 t) {
    TVBase that = (TVBase)t;    // Invariant when called
    that._t = that._t.meet(_t);
  }
  
  @Override boolean _unify_impl(TV3 t ) { return true; }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 that, boolean test) {
    TVBase base = (TVBase)that;
    add_delay_fresh();          // If this Base can fall, must fresh-unify that Base
    Type t = _t.meet(base._t);
    if( t==base._t && (!WIDEN_FRESH || t==_t) ) return false;
    if( test ) return true;
    if( base._t != t ) base.move_delay(); // Any Fresh base updates need to rerun
    base._t = t;
    if( WIDEN_FRESH ) {
      if( _t != t ) move_delay(); // Any Fresh base updates need to rerun
      _t = t;
    }
    return true;
  }


  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3 ) {
    TVBase that = (TVBase)tv3; // Invariant when called
    // Unifies OK if bases will unify, e.g. both ints or both floats
    return _t.getClass() == that._t.getClass();
  }

  // Unifies if same and cannot fall
  @Override boolean _exact_unify_impl( TV3 tv3 ) {
    TVBase base = (TVBase)tv3;
    return _t == base._t;
  }

  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { return _t; }
  @Override void _widen( byte widen ) {
    if( widen < 2 ) return;
    Type tw = _t.widen();
    if( tw == _t ) return;
    _t = tw;
    _deps_work_clear();
  }
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) { return sb.p(_t); }  
}
