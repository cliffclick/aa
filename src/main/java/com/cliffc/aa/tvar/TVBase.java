package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

public class TVBase extends TV3 {
  public Type _t;  
  private TVBase( boolean is_copy, Type t ) {
    super(is_copy, (TV3[]) null);
    assert t!=Type.ALL;
    _t = t;
  }
  public static TV3 make( boolean is_copy, Type t) {
    return t==Type.ALL ? new TVLeaf(is_copy) : new TVBase(is_copy,t);
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

  // Convert the leader nil into a base+XNIL, widened if the leader is not a
  // copy.
  @Override TV3 find_nil( TVNil nil ) {
    throw unimpl();
  }
  
  // -------------------------------------------------------------
  @Override void _union_impl(TV3 t) {
    TVBase that = (TVBase)t;
    that._t = that._t.meet(_t);
  }
  
  @Override boolean _unify_impl(TV3 t ) { return union(t); }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 that, TV3[] nongen, boolean test) {
    TVBase base = (TVBase)that;
    Type t = _t.meet(base._t);
    if( t==base._t ) return false;
    if( !test ) base._t = t;
    return true;
  }


  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVBase that = (TVBase)tv3; // Invariant when called
    // Unifies OK if bases will unify, e.g. both ints or both floats
    return _t.getClass() == that._t.getClass();
  }
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { return _t; }  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) { return sb.p(_t); }  
}
