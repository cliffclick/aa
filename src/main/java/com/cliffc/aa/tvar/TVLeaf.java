package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;

import static com.cliffc.aa.AA.unimpl;

public class TVLeaf extends TV3 {

  public TVLeaf() { }
  public TVLeaf( boolean is_copy ) { super(is_copy); }

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
    return Env.ROOT.ext_scalar(dep);
  }  
}
