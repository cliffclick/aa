package com.cliffc.aa.tvar;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

public class TVBase extends TVNilable {
  public Type _t;  
  private TVBase( boolean is_copy, Type t ) {
    super(is_copy,false, (TV3[]) null);
    assert t!=Type.ALL;
    _t = t;
  }
  public static TV3 make( boolean is_copy, Type t) {
    return t==Type.ALL ? new TVLeaf(is_copy) : new TVBase(is_copy,t);
  }
  
  // -------------------------------------------------------------
  @Override
  void _union_impl(TV3 t) {
    TVBase that = (TVBase)t;
    that._t = that._t.meet(_t);
  }
  
  @Override boolean _unify_impl(TV3 t ) { return union(t); }

  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVBase that = (TVBase)tv3; // Invariant when called
    // Unifies OK if bases will unify, e.g. both ints or both floats
    return _t.getClass() == that._t.getClass();
  }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) { return sb.p(_t); }  
}
