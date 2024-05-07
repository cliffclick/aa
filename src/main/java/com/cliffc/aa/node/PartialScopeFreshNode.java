package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

// "fresh" the incoming TVar: make a fresh instance before unifying
public class PartialScopeFreshNode extends FreshNode {
  final int _alias;
  final String[] _flds;

  public PartialScopeFreshNode( ScopeNode scope ) {
    super(scope.ptr());
    _alias = scope.ptr()._alias;
    StructNode frame = scope.stk();
    // Copy partial list of field names
    _flds = new String[frame.len()];
    for( int i=0; i<frame.len(); i++ )
      _flds[i] = frame.fld(i);
  }

  @Override public String label() { return "PartialScopeFresh"; }
  @Override public Type value() {
    // ptr-to-partial struct
    return TypeMemPtr.make(_alias,TypeStruct.ISUSED);
  }

  @Override public Type live_use( int i ) {
    if( i != 0 ) return Type.ALL;
    return val(0) instanceof TypeMemPtr tmp
      ? tmp._obj.flatten_live_fields()
      : val(0).oob();
  }

  @Override public TV3 _set_tvar() {
    // Close any cycles with an early set
    TVStruct partial = new TVStruct(_flds,TVStruct.leafs(_flds.length),true);
    TVPtr ptr = new TVPtr(BitsAlias.make0(_alias),partial);
    _tvar = ptr;

    // Make sure the shared closure is set_tvar
    in(0).set_tvar();
    // Do a first unify
    unify(false);
    return ptr;
  }

  @Override public boolean unify( boolean test ) {
    if( !(tvar(0) instanceof TVPtr ptr) ) throw AA.TODO();
    TVStruct fresh = ptr.load();
    TV3[] tvs = new TV3[_flds.length];
    for( int i=0; i<_flds.length; i++ ) {
      tvs[i] = fresh.arg(_flds[i]);
      if( tvs[i] == null )
        tvs[i] = Util.eq(_flds[i],TypeFld.CLZ)
          ? new TVPtr(BitsAlias.EMPTY, new TVStruct(true) )
          : new TVLeaf();
    }
    TVStruct partial = new TVStruct(_flds,tvs,true);
    TVStruct that = ((TVPtr)tvar()).load();
    return partial.fresh_unify(_nongen,that,test);
  }
}
