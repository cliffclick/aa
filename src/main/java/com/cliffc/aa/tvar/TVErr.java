package com.cliffc.aa.tvar;

import static com.cliffc.aa.AA.unimpl;

/** A type error.  A collection of un-unifiable TV3s
 *
 */
public class TVErr extends TV3 {

  // Return a TV3 for a bound lambda
  public TVLambda as_lambda() {
    throw unimpl();
  }
  
  // -------------------------------------------------------------
  @Override
  void _union_impl(TV3 that) {
    if( !(that instanceof TVErr err) ) throw unimpl();
    throw unimpl();
  }

  @Override boolean _unify_impl(TV3 that ) {
    throw unimpl();
  }
}
