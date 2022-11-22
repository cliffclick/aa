package com.cliffc.aa.tvar;

import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** A TV3 which might also be nil.  Ptr, Base, Lambda can be nil.
 *  Struct, Leaf, Field, Err cannot.
 */
public abstract class TVNilable extends TV3 {
  boolean _may_nil;
  public TVNilable( boolean is_copy, boolean may_nil, TV3... tv3s ) { super(is_copy,tv3s); _may_nil=may_nil; }
}
