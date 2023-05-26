package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
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

  @Override int eidx() { return TVErr.XNIL; }
  @Override public TVNil as_nil() { return this; }
  
  // -------------------------------------------------------------
  // No sub-parts to union
  @Override public void _union_impl(TV3 that) { }

  @Override boolean _unify_impl(TV3 that ) { return arg(0)._unify(that.arg(0),false); }

  // U-F union; this is nilable and this becomes that.
  // No change if only testing, and reports progress.
  // Same as HM unify_nil.
  boolean _unify_nil( TV3 that, boolean test ) {
    if( test ) return true;     // Will make progress in all situations
    TVLeaf not_nil = not_nil();
    assert !not_nil._may_nil; // might not be true under nested nilables, not required since copy strips nil
    not_nil._deps_work_clear();
    TV3 copy = that.copy().strip_nil();
    not_nil.union(copy);
    union(that);
    TV3 rez = that.find_nil();
    that._unify(rez,false);
    return true;
  }

  // U-F union; this is nilable and a fresh copy of this unifies to that.
  // No change if only testing, and reports progress.
  // Same as HM.unify_nil.
  //
  // Example: Some number of PTRs point to THAT which points onward.
  //   {PTR*} -->  THAT  --> {THAT._ARGS}
  // We need the PTRs to "see thru" a Nil to pick up the possible-nil.
  // Find_nil will actually install the nil on the PTRs' views, while direct
  // pointers to THAT._ARGS will continue to see the not-nil flavor.
  //   {PTR*} -->  {THAT>>COPY} --> {THAT.ARGS}  
  boolean _unify_nil_l( TV3 that, boolean test ) {
    assert !(that instanceof TVNil) && !not_nil()._may_nil;
    return that.add_may_nil(test);
  }

  // U-F union; this is nilable and a fresh copy of that unifies to this.
  // Handle cycles in the fresh side, by calling _fresh instead of copy.
  // No change if only testing, and reports progress.
  // Same as HM.unify_nil_r.
  TV3 _unify_nil_r( TV3 that, boolean test ) {
    assert !(that instanceof TVNil);
    if( test ) return that;     // Will make progress in all situations
    TVLeaf not_nil = not_nil();
    assert !not_nil._may_nil; // might not be true under nested nilables, not required since copy strips nil
    // A shallow copy and fresh-unify fails if 'this' is cyclic, because the
    // shallow copy peels one part of the loop.
    TV3 copy = that._fresh().strip_nil();
    not_nil.union(copy);
    return copy;
  }


  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 that ) {
    if( that instanceof TVNil ) return true;
    if( that instanceof TVBase base && base._t.must_nil() )
    // Some primitives will unify with NIL
      return true;
    if( that instanceof TVStruct ts ) {
      //TV3 self = ts.arg(TypeStruct.SELF);
      //if( self==null ) return false;
      //return _trial_unify_ok_impl(self,extras);
      throw unimpl();
    }
    return false;
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { throw unimpl(); }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    Type t = not_nil()._as_flow(dep);
    return t.meet(TypeNil.NIL);
  }
  @Override void _widen( byte widen ) {
    not_nil().widen(widen,false);
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    return _args[0]._str(sb,visit,dups,debug,prims).p('?');
  }  
}
