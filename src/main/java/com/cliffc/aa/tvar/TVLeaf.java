package com.cliffc.aa.tvar;

public class TVLeaf extends TV3 {

  // -------------------------------------------------------------
  @Override boolean _unify_impl(TV3 that, boolean test ) {
    // Always fold leaf into the other.
    // If that is ALSO a Leaf, keep the lowest UID.
    return that instanceof TVLeaf leaf && _uid < that._uid
      ? leaf.union(this,test)
      : this.union(that,test);
  }

  // Leafs have no subclass specific parts to union
  @Override void _union_impl(TV3 that) { }
}
