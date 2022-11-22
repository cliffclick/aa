package com.cliffc.aa.tvar;

import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** Field reference from a Struct
 */
public class TVField extends TV3 {
  
  public TVField( TV3 ptr ) { super(true,ptr); }

  // True if this field is still resolving: the actual field being referenced
  // is not yet known.
  static boolean is_resolving(String id) { return id.charAt(0)=='&'; }

  // -------------------------------------------------------------
  @Override void _union_impl(TV3 that) {
    if( !(that instanceof TVBase base) ) throw unimpl();
    throw unimpl();
  }
  
  @Override boolean _unify_impl(TV3 that, boolean test ) {
    throw unimpl();
  }
}
