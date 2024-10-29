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
  // Already a constant
  @Override public boolean shouldCon() { return false; }

  @Override public Type value() { return _t; }

  @Override public boolean has_tvar() {
    if( _t instanceof TypeNil &&
        (!_t.above_center() || _t==TypeNil.NIL ) ) // Allow both flavors of NIL
      return true; // Yes on NIL, INT, FLT, MEMPTR, FUNPTR, STRUCT
    // No for TFLD, RPC
    return false;
  }


  // Constants.  You'd think "ConNode" and constant Type and be done, but no....

  // Each constant has a copy - a *FRESH* copy of the associated class baked
  // into associated phat prim value.  Example for int:17:
  //   *[INTX]{ ^ = @{INTCLZ}, _ = int:17 }
  // This is a *fresh* copy of the integer clazz.  However, the integer clazz
  // has no type variables, so fresh-or-not makes no difference.
  //
  // However, the NIL clazz is full of type variables
  @Override public TV3 _set_tvar() {
    unelock();                  // Hash now depends on TVars
    TV3 tv = TV3.from_flow(_t);
    tv.deps_add_deep(this);     // Constant hash depends on tvar
    return tv;
  }

  private boolean equals_uses_tvar() {
    return _t==TypeNil.NIL || _t instanceof TypeMemPtr || _t instanceof TypeFunPtr;
  }
  @Override int hash() {
    // In theory also slot 0, but slot 0 is always Root.
    return _t.hashCode();
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
