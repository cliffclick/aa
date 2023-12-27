package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.*;

// Constant value nodes; no computation needed.  Hashconsed for unique
// constants, except for XNIL.  XNIL allows for a TV3 typevar Nilable-Leaf with
// each Leaf unifying on its own.
public class ConNode<T extends Type> extends Node {
  public T _t;                  // Not final for testing
  public ConNode( T t ) {
    super(Env.ROOT);
    _t=t;
    if( !Combo.pre() && has_tvar() )
      _tvar = TV3.from_flow(_t);
  }
  @Override public String label() {
    return _t==null ? "(null)" : _t.toString();
  }
  @Override public boolean isMem() { return _t instanceof TypeMem; }

  @Override public Type value() { return _t; }

  @Override public boolean has_tvar() {
    if( _t==Type.ALL || _t==Type.ANY ) return true;  // Specifically allowed for various unused-displays on primitives
    if( _t instanceof TypeNil ) return true; // Yes on NIL, INT, FLT, MEMPTR, FUNPTR, STRUCT
    // No for TFLD, RPC
    return false;
  }

  @Override public TV3 _set_tvar() {
    unelock();                  // Hash now depends on TVars
    TV3 tv = TV3.from_flow(_t);
    tv.deps_add_deep(this);     // Constant hash depends on tvar      
    return tv;
  }

  private boolean equals_uses_tvar() {
    return _t==TypeNil.NIL || _t instanceof TypeMemPtr || _t instanceof TypeFunPtr;
  }
  @Override public int hashCode() {
    // In theory also slot 0, but slot 0 is always Start.
    int hash = _t.hashCode();
    // Two NILs are typically different because their TV3s are different.
    // Also, vary two TMPs or TFPs might vary (but not e.g. Scalar)
    if( _tvar!=null && has_tvar() )
      hash ^= _tvar._uid;
    return hash;
  }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConNode con) ) return false;
    if( _t!=con._t ) return false;
    if( _tvar!=null ) return tvar()==con.tvar();
    // Prior to Combo we must assume two NILs will unify to different TV3
    // types and thus must remain separate.  After Combo they can fold together
    // if they have the same TVars.
    return !has_tvar();
  }
  
  //@Override Node walk_dom_last( Predicate<Node> P) { return null; }
}
