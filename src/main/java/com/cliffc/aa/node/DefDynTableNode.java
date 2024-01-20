package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.*;

// A DefDynTable.  Type is unknown until Combo, so set super conservative
// before then.  Value will eventually be a constant, but has special
// rules around tvars
public class DefDynTableNode extends Node {
  public DefDynTableNode( ) {
    super(Env.ROOT);
  }
  @Override public String label() { return "DynTable";  }
  @Override public boolean isMem() { return false; }
  @Override public boolean shouldCon() { return false; }
  @Override public Type value() {
    // Value depends on tvar, which requires combo.
    // Needs a TypeStruct variant of TVDynTable
    throw AA.TODO();
  }

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() { return new TVLeaf(); }

  @Override public boolean unify( boolean test ) {
    throw AA.TODO();
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
