package com.cliffc.aa.tvar;

import com.cliffc.aa.util.*;

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
  
  public TVNil( TV3 tv3 ) { super(true,tv3); }
  public TV3 not_nil() { return arg(0); }
  
  public TV3 find_nil() { throw unimpl(); }

  // -------------------------------------------------------------
  @Override
  void _union_impl(TV3 that) {
    if( !(that instanceof TVBase base) ) throw unimpl();
    throw unimpl();
  }

  @Override boolean _unify_impl(TV3 that ) {
    throw unimpl();
  }

  @Override int eidx() { throw unimpl(); }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb,visit,dups,debug).p('?');
  }  
}
