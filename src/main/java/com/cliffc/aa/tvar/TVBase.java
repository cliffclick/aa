package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
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
  @Override boolean add_nil(boolean test) {
    Type t = _t.meet(TypeNil.NIL);
    if( test ) return t!=_t || !_may_nil;
    _t = t;
    return (_may_nil = true);
  }

  // Convert the leader nil into a base+NIL, widened if the leader is not a
  // copy.
  @Override TV3 find_nil( TVNil nil ) {
    Type t = _t.meet(TypeNil.NIL);
    if( !nil._is_copy ) t = t.widen(); // Widen if leader is a not a copy
    if( t==_t && _may_nil && (!_is_copy || nil._is_copy) )
      return this;
    // Need a new base, because either t or is_copy or may_nil changes
    TVBase b = new TVBase(_is_copy & nil._is_copy,t);
    b._may_nil = true;
    return b;
  }
  
  // -------------------------------------------------------------
  @Override void _union_impl(TV3 t) {
    TVBase that = (TVBase)t;    // Invariant when called
    that._t = that._t.meet(_t);
  }
  
  @Override boolean _unify_impl(TV3 t ) { return true; }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 that, boolean test) {
    TVBase base = (TVBase)that;
    add_delay_fresh();          // If this Base can fall, must fresh-unify that Base
    Type t = _t.meet(base._t);
    if( t==base._t ) return false;
    if( !test ) {
      base._t = t;
      base.move_delay_fresh();  // Any Fresh base updates need to rerun
    }
    return true;
  }


  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVBase that = (TVBase)tv3; // Invariant when called
    // Unifies OK if bases will unify, e.g. both ints or both floats
    if( _t.getClass() != that._t.getClass() ) return false;
    return Resolvable.add_pat_leaf(this);
  }

  // -------------------------------------------------------------
  private Ary<TVStruct> _delay_resolve;
  void delay_resolve(TVStruct tvs) {
    if( _delay_resolve==null ) _delay_resolve = new Ary<>(new TVStruct[1],0);
    if( _delay_resolve.find(tvs)== -1 )
      _delay_resolve.push(tvs);
  }

  @Override void move_delay_resolve() { DELAY_RESOLVE.addAll(_delay_resolve); }
 
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { return _t; }  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) { return sb.p(_t); }  
}
