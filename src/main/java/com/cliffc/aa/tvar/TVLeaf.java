package com.cliffc.aa.tvar;

public class TVLeaf extends TV3 {

  public TVLeaf() { }
  public TVLeaf( boolean is_copy ) { super(is_copy); }
  
  // -------------------------------------------------------------
  @Override boolean _unify_impl(TV3 that ) {
    // Always fold leaf into the other.
    // If that is ALSO a Leaf, keep the lowest UID.
    assert !(that instanceof TVLeaf leaf && _uid < that._uid);
    return this.union(that);
  }

  // Leafs have no subclass specific parts to union
  @Override
  void _union_impl(TV3 that) {
  }
}
