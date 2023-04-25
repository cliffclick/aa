package com.cliffc.aa.tvar;

import com.cliffc.aa.AA;
import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeNil;

import static com.cliffc.aa.AA.unimpl;

public class TVLeaf extends TV3 {

  @Override boolean can_progress() { return false; }
  
  // Leafs never show up in errors
  @Override int eidx() { throw unimpl(); }

  // No improvement, return the not-nil leader
  @Override TV3 find_nil() { throw unimpl(); }

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
  @Override public boolean _union_impl(TV3 that) { return false; }

  // Always unifies
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) { return true; }

  // Never unifies
  @Override boolean _exact_unify_impl( TV3 tv3 ) { return false; }
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    if( Combo.HM_FREEZE ) return Env.ROOT.ext_scalar(dep);
    Combo.add_freeze_dep(dep);
    deps_add(dep);
    return (AA.DO_HMT || !_use_nil) ? TypeNil.XSCALAR : TypeNil.AND_XSCALAR;
  }
  @Override void _widen( byte widen ) { }

}
