package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVDynTable;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;

// Extract an "apply" (or CallNode) field from a DynTable input
public class AFieldNode extends Node {
  public AFieldNode( Node dyn ) { super(dyn); }
  @Override public String label() { return "AField";  }
  @Override public Type value() {
    // Weak-in means weak-out
    Type t = val(0);
    if( !(t instanceof TypeStruct ts) )
      return t;
    if( ts == TypeStruct.DYNTABLE )
      return TypeStruct.DYNTABLE;
    throw AA.TODO();
  }

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    _tvar = new TVLeaf();
    TV3 ptr = in(0).set_tvar();
    TVDynTable ptrdyn;
    if( ptr instanceof TVDynTable tdyn0 ) ptrdyn = tdyn0;
    else  ptr.unify(ptrdyn = new TVDynTable(),false);

    TV3 tv3 = tvar();
    TV3 self = ptrdyn.find_apy(this);
    if( self==null ) ptrdyn.add_apy(this,tv3);
    else             assert self==tv3;

    ptrdyn.resolve(false);
    return tv3;
  }
  
  // No CSE, depends on the following Call.
  // Really is an edge helper can could be folded into the Call itself
  @Override int hash() {
    return _uid;
  }
  @Override public boolean equals(Object o) {
    return this == o;
  }

}
