package com.cliffc.aa.tvar;

import com.cliffc.aa.type.TypeNil;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

/** Polymorphic nil.
 * <p>
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
  @Override void _union_impl(TV3 that) { }

  @Override boolean _unify_impl(TV3 that ) { throw unimpl(); }

  boolean _unify_nil( TV3 that, boolean test ) {
    if( test ) return true;     // Will make progress in all situations
    TVLeaf not_nil = not_nil();
    not_nil._deps_work_clear();
    TV3 copy = that.copy().strip_nil();
    _is_copy &= that._is_copy;
    not_nil.union(copy);
    if( that instanceof TVBase ) this.union(that); // Can reverse and turn into a Base
    else that.union(this);      // Force 'that' to be nil-able version
    return true;
  }

  // same as HM w/nongten, except this & that reversed
  boolean _unify_nil( TV3 that, TV3[] nongen, boolean test ) {
    assert !(that instanceof TVNil);
    if( test ) return true;     // Will make progress in all situations
    TVLeaf not_nil = not_nil();
    not_nil._deps_work_clear();
    // A shallow copy and fresh-unify fails if 'this' is cyclic, because the
    // shallow copy peels one part of the loop.
    TV3 copy = that._fresh(nongen).strip_nil();
    _is_copy &= that._is_copy;
    not_nil.union(copy);
    if( that instanceof TVBase ) this.union(that); // Can reverse and turn into a Base
    else that.union(this);      // Force 'that' to be nil-able version
    return true;
  }

  boolean _fresh_unify_nil( TV3 that, boolean test ) {
    assert !(that instanceof TVNil);
    if( that instanceof TVBase base ) {
      TypeNil t = (TypeNil)base._t.meet(TypeNil.XNIL);
      if( base._t == t ) return false;
      if( !test ) base._t = t;
      return true;
    }
    //TVLeaf not_nil = not_nil();
    //not_nil._deps_work_clear();
    //TV3 copy = that.copy().strip_nil();
    //_is_copy &= that._is_copy;
    //not_nil.union(copy);
    //if( that instanceof TVBase ) this.union(that); // Can reverse and turn into a Base
    //else that.union(this);      // Force 'that' to be nil-able version
    //return true;
    throw unimpl();
  }

  
  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 that, boolean extras ) {
    if( that instanceof TVNil ) return true;
    if( that instanceof TVBase base &&
        base._t.must_nil() )
      return true;
    return false;
  }
  
  // -------------------------------------------------------------
  @Override int eidx() { throw unimpl(); }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb,visit,dups,debug).p('?');
  }  
}
