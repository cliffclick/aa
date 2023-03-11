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
  
  public TVNil( TV3 tv3 ) { super(true,tv3); _may_nil = true; }
  public TVLeaf not_nil() { return (TVLeaf)arg(0); }

  @Override int eidx() { return TVErr.XNIL; }
  @Override public TVNil as_nil() { return this; }
  
  // -------------------------------------------------------------
  // No sub-parts to union
  @Override void _union_impl(TV3 that) { }

  @Override boolean _unify_impl(TV3 that ) { return arg(0)._unify(that.arg(0),false); }

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

  // same as HM w/nongen, except this & that reversed
  boolean _unify_nil_r( TV3 that, boolean test ) {
    assert !(that instanceof TVNil);
    if( test ) return true;     // Will make progress in all situations
    TVLeaf not_nil = not_nil();
    not_nil._deps_work_clear();
    // A shallow copy and fresh-unify fails if 'this' is cyclic, because the
    // shallow copy peels one part of the loop.
    TV3 copy = that._fresh().strip_nil();
    _is_copy &= that._is_copy;
    not_nil.union(copy);
    if( that instanceof TVBase ) this.union(that); // Can reverse and turn into a Base
    else that.union(this);      // Force 'that' to be nil-able version
    return true;
  }


  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 that, boolean extras ) {
    if( that instanceof TVNil ) return true;
    if( that instanceof TVBase base && base._t.must_nil() )
      return true;
    // Nil-check against the instance, not the clazz
    if( that instanceof TVClz clz ) 
      return _trial_unify_ok_impl(clz.rhs(),extras);
    // Some primitives will unify with NIL
    if( that instanceof TVStruct ts ) {
      //TV3 self = ts.arg(TypeStruct.SELF);
      //if( self==null ) return false;
      //return _trial_unify_ok_impl(self,extras);
      throw unimpl();
    }
    return false;
  }
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    Type t = not_nil()._as_flow(dep);
    return t.meet(TypeNil.NIL);
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb,visit,dups,debug).p('?');
  }  
}
