package com.cliffc.aa.tvar;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

public class TVBase extends TVNilable {
  public final Type _t;  
  public TVBase( boolean is_copy, Type t ) { super(is_copy,false); _t = t; }
  
  // -------------------------------------------------------------
  @Override void _union_impl(TV3 that) {
    if( !(that instanceof TVBase base) ) throw unimpl();
    throw unimpl();
  }
  
  @Override boolean _unify_impl(TV3 that, boolean test ) { throw unimpl(); }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) { return sb.p(_t); }  
}
