package com.cliffc.aa.tvar;

import static com.cliffc.aa.AA.unimpl;

/** Polymorphic nil.
 *
 *  TVNils are nilable versions of other, not-nil things.  Used after nil guard
 *  tests to assert nilable properties.  This is similar to the GCP not-nil
 *  flow property, except its on H-M typing and thus survives e.g. polymorphic
 *  map calls.  This is similar to wrapping with e.g. Option or Maybe, except
 *  it is guarenteed zero-cost at any level of wrapping.
 */
public class TVNil extends TV3 {
  
  public TVNil( TV3 tv3 ) {
    _args = new TV3[]{tv3};
  }
  TV3 find_nil() { throw unimpl(); }
}
