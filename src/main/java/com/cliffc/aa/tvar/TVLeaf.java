package com.cliffc.aa.tvar;

import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.unimpl;

public class TVLeaf extends TV3 {

  public TVLeaf() { }
  public TVLeaf( boolean is_copy ) { super(is_copy); }

  // This Leaf is used Fresh against another TV3.
  // If it ever unifies to not-Leaf, we need to re-Fresh the deps.
  Ary<TV3  > _delay_fresh_deps;
  Ary<TV3[]> _delay_fresh_nongen;

  // Record t on the delayed fresh list, and return that.  If `this` every
  // unifies to something, we need to Fresh-unify the something with `that`.
  TV3 delay_fresh(TV3 that, TV3[] nongen) {
    if( _delay_fresh_deps==null ) {
      _delay_fresh_deps   = new Ary<>(new TV3[]  {that  });
      _delay_fresh_nongen = new Ary<>(new TV3[][]{nongen});
    }
    if( _delay_fresh_deps.find(that)==-1 ) {
      _delay_fresh_deps  .push(that  );
      _delay_fresh_nongen.push(nongen);
    }
    assert _delay_fresh_deps.len()<=10; // Switch to worklist format
    return that;
  }
  
  TV3 find_nil(TVNil nil) { return nil; }

  // -------------------------------------------------------------
  @Override boolean _unify_impl(TV3 that ) {
    // Always fold leaf into the other.
    // If that is ALSO a Leaf, keep the lowest UID.
    assert !(that instanceof TVLeaf leaf) || _uid > that._uid;
    // Leafs must call union themselves; other callers of _unify_impl get a
    // union call done for them.
    return this.union(that);
  }

  // Leafs have no subclass specific parts to union.  However, if the Leaf was
  // a LHS of a Fresh, and is now becoming `that`, then everything the old Leaf
  // was Fresh'd against now needs to be Fresh'd against `that`.
  @Override void _union_impl(TV3 that) {
    if( _delay_fresh_deps != null )
      for( int i=0; i<_delay_fresh_deps._len; i++ ) {
        DELAY_FRESH_THIS  .push(this);
        DELAY_FRESH_THAT  .push(_delay_fresh_deps  .at(i));
        DELAY_FRESH_NONGEN.push(_delay_fresh_nongen.at(i));
      }
  }

  // Always unifies
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) { return true; }

  // -------------------------------------------------------------
  @Override int eidx() { throw unimpl(); }

}
