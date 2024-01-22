package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;

// A DefDynTable.  Type is unknown until Combo, so set very conservative
// before then.  Value will eventually be a constant, but has special
// rules around tvars.
public class DefDynTableNode extends Node {
  public DefDynTableNode( ) {
    super(Env.ROOT);
  }
  @Override public String label() { return "DynTable";  }
  @Override public boolean shouldCon() { return false; }
  @Override public Type value() {
    // Value depends on tvar, which requires combo.
    if( Combo.pre() )
      return TypeStruct.DYNTABLE;
    // Needs a TypeStruct variant of TVDynTable.
    // TODO: For now, just be conservative
    return TypeStruct.DYNTABLE;
  }

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() { return new TVLeaf(); }

  @Override public boolean unify( boolean test ) {
    return tvar() instanceof TVDynTable tdyn && tdyn.resolve(test);
  }

  // Never GVN until after Combo
  @Override int hash() {
    if( Combo.pre() ) return _uid;
    return _tvar._uid;
  }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof DefDynTableNode dyn) ) return false;
    if( Combo.pre() ) return false;
    if( _tvar == dyn._tvar )
      throw AA.TODO("UNTESTED FOLDING 2 EQUAL DYNTABLES");  //return true;
    return false;
  }
}
