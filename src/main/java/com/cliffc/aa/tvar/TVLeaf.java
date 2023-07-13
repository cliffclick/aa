package com.cliffc.aa.tvar;

import com.cliffc.aa.AA;
import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeNil;

import static com.cliffc.aa.AA.unimpl;

public class TVLeaf extends TVExpanding {

  // Leafs can unify and thus make progress, but then tney are not a Leaf
  // anymore.  At some point, all possible unifications may have happened to a
  // Leaf, and if it could have progressed - it would have.  At this point we
  // can declare the Leaf makes no more progress.

  // This matters for Resolving and trial_unify, as a progress-able Leaf is a
  // Maybe, but a no-progress Leaf will never fail a trial and so is a Yes.
  private boolean _no_progress;
  @Override boolean can_progress() { return !_no_progress; }
  public void set_no_progress() { _no_progress=true; }
  
  // Leafs never show up in errors
  @Override int eidx() { throw unimpl(); }

  // -------------------------------------------------------------
  @Override boolean _unify_impl(TV3 that ) {
    // Always fold leaf into the other.
    // If that is ALSO a Leaf, keep the lowest UID.
    assert !(that instanceof TVLeaf) || _uid > that._uid;
    // Leafs must call union themselves; other callers of _unify_impl get a
    // union call done for them.
    return this.union(that);
  }
  
  // Leafs have no subclass specific parts to union.
  @Override public void _union_impl(TV3 that) { }

  // Merge deps from this into that
  @Override public void _union_deps(TV3 that) {
    if( that._deps==null ) that._deps = _deps;
    else that._deps.addAll(_deps);
  }

  // Always maybe unifies
  @Override int _trial_unify_ok_impl( TV3 tv3 ) { return 0; }

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
