package com.cliffc.aa.tvar;

import com.cliffc.aa.AA;
import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeNil;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.unimpl;

public class TVLeaf extends TV3 {

  public TVLeaf() { }
  public TVLeaf( boolean is_copy ) { super(is_copy); }

  private Ary<TVStruct> _delay_resolve;

  // Leafs never show up in errors
  @Override int eidx() { throw unimpl(); }

  // No improvement, return the not-nil leader
  @Override TV3 find_nil(TVNil nil) { return nil; }

  // -------------------------------------------------------------
  @Override boolean _unify_impl(TV3 that ) {
    // Always fold leaf into the other.
    // If that is ALSO a Leaf, keep the lowest UID.
    assert !(that instanceof TVLeaf leaf) || _uid > that._uid;
    // Leafs must call union themselves; other callers of _unify_impl get a
    // union call done for them.
    return this.union(that);
  }

  // Leafs have no subclass specific parts to union.
  @Override void _union_impl(TV3 that) { }

  // Always unifies
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) { return true; }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    if( Combo.HM_FREEZE ) return Env.ROOT.ext_scalar(dep);
    Combo.add_freeze_dep(dep);
    return (AA.DO_HMT || !_use_nil) ? TypeNil.XSCALAR : TypeNil.AND_XSCALAR;
  }

  // -------------------------------------------------------------
  void delay_resolve(TVStruct tvs) {
    if( _delay_resolve==null ) _delay_resolve = new Ary<>(new TVStruct[1],0);
    if( _delay_resolve.find(tvs)== -1 )
      _delay_resolve.push(tvs);
  }

  @Override void move_delay_resolve() { DELAY_RESOLVE.addAll(_delay_resolve); }
  
}
