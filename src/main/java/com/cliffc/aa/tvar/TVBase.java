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
    Type foo = that._t.meet(_t);
    that._t = foo;
  }
  
  @Override boolean _unify_impl(TV3 t ) { return union(t); }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) { return sb.p(_t); }  
}
