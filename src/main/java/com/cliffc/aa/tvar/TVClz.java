package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

/** Subclassing.  LHS is a struct representing a clazz; RHS is an instance.
 * <p> 
 *  LHS is the clazz struct; a collection of final constant fields available in
 *  field lookups on the RHS.  RHS can be anything, include "int" or a struct.
 */
public class TVClz extends TV3 {
  
  public TVClz( TVStruct clz, TV3 rhs ) { super(clz,rhs); }
  public TVStruct clz() { return (TVStruct)arg(0); }
  public TV3      rhs() { return           arg(1); }

  @Override boolean can_progress() { return false; }
  @Override int eidx() { return TVErr.XCLZ; }
  @Override public TVClz as_clz() { return this; }

  @Override TV3 strip_nil() {
    _args[1] = rhs().copy().strip_nil();
    _may_nil = false;
    return this;
  }
  @Override boolean add_may_nil(boolean test) {
    if( _may_nil && !rhs().add_may_nil(true) ) return false;
    if( test ) return true;
    _args[1] = rhs().copy();
    _args[1].add_may_nil(false);
    super.add_may_nil(false);
    return true;
  }

  
  // Keep the Clz wrapper, but find_nil the instance
  @Override TV3 find_nil( ) {
    TV3 nn = rhs().find_nil();
    if( nn == rhs() )
      return this; // No change so just use same Clz
    return new TVClz(clz(),nn);
  }

  // -------------------------------------------------------------
  @Override public void _union_impl(TV3 that) { }

  @Override boolean _unify_impl(TV3 t ) {
    TVClz clz = (TVClz)t;       // Invariant when called
    return clz()._unify(clz.clz(),false) | ((TVClz)find()).rhs()._unify(((TVClz)clz.find()).rhs(),false);
  }


  
  // -------------------------------------------------------------
  
  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVClz clz = (TVClz)tv3;     // Invariant when called
    return
      clz()._trial_unify_ok(clz.clz(),extras) &&
      rhs()._trial_unify_ok(clz.rhs(),extras);
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { throw unimpl(); }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    TVStruct clz = arg(0).as_struct();
    Type rhs = rhs()._as_flow(dep);
    if( clz.is_int_clz() || clz.is_flt_clz() ) return rhs;
    // Need to return a flow-type with this unnamed inferred clazz; also I do
    // not know the instance type either.
    if( clz.is_str_clz() )
      throw unimpl();
    // TODO: Add clazz to structs
    return rhs;
  }
  @Override void _widen( byte widen ) {
    clz().widen((byte)1,false);
    rhs().widen(widen  ,false);
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    clz()._str(sb,visit,dups,debug,prims).p(':');
    return rhs()._str(sb,visit,dups,debug,prims);
  }  
}
