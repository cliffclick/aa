package com.cliffc.aa.tvar;

import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** Polymorphic nil.
 *
 *  TVNils are nilable versions of other, not-nil things.  Used after nil guard
 *  tests to assert nilable properties.  This is similar to the GCP not-nil
 *  flow property, except its on H-M typing and thus survives e.g. polymorphic
 *  map calls.  This is similar to wrapping with e.g. Option or Maybe, except
 *  it is guaranteed zero-cost at any level of wrapping.
 */
public class TVNil extends TV3 {
  
  public TVNil( TV3 tv3 ) { super(true,tv3); }
  public TVLeaf not_nil() { return (TVLeaf)arg(0); }
  
  public TV3 find_nil() { throw unimpl(); }

  // -------------------------------------------------------------
  @Override void _union_impl(TV3 that) { throw unimpl(); }

  @Override boolean _unify_impl(TV3 that ) { throw unimpl(); }

  boolean _unify_nil( TV3 that, boolean test ) {
    if( test ) return true;     // Will make progress in all situations
    TVLeaf not_nil = not_nil();
    not_nil._deps_work_clear();
    TV3 copy = that.copy().strip_nil();
    _is_copy &= that._is_copy;
    return not_nil.union(copy) | that.union(this);
  }
  
  @Override int eidx() { throw unimpl(); }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb,visit,dups,debug).p('?');
  }  
}
