package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.FreshNode;
import com.cliffc.aa.util.Ary;

import java.util.Arrays;

import static com.cliffc.aa.AA.TODO;

abstract public class TVExpanding extends TV3 {

  TVExpanding() { this(null); }
  TVExpanding( TV3[]tvs ) { super(tvs); }

  // True if this TV3 can progress in-place.
  // Leafs unify and so become some other thing - so cannot update-in-place.
  // Ptr/Bases can fall, until the Type hits bottom, e.g. TypeInt.INT64.
  // Structs can add fields while open, can close, and then can remove fields
  // until empty.
  abstract boolean can_progress();
}
