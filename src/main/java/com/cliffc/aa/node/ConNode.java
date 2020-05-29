package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

public class ConNode<T extends Type> extends Node {
  T _t;                         // Not final for testing
  public ConNode( T t ) { super(OP_CON,Env.START); _t=t; }
  // Used by FunPtrNode
  ConNode( byte type, T tfp, RetNode ret, Node closure ) { super(type,ret,closure); _t = tfp; }
  @Override String xstr() { return Env.ALL_CTRL == this ? "ALL_CTL" : _t.toString(); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    // ALL_CTRL is used for unknown callers; during and after GCP there are no
    // unknown callers.  However, we keep the ALL_CTRL for primitives so we can
    // reset the compilation state easily.
    if( gvn._opt_mode>=2 && Env.ALL_CTRL == this ) return Type.XCTRL;
    return _t;
  }
  @Override public TypeMem live( GVNGCM gvn) {
    // If any use is alive, the Con is alive... but it never demands memory.
    // Indeed, it may supply memory.
    for( Node use : _uses )
      if( use.live_use(gvn, this) != TypeMem.DEAD )
        return TypeMem.EMPTY;
    return TypeMem.DEAD;
  }
  @Override public String toString() { return str(); }
  @Override public int hashCode() { return _t.hashCode(); }// In theory also slot 0, but slot 0 is always Start
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConNode) ) return false;
    ConNode con = (ConNode)o;
    return _t==con._t;
  }
  @Override public byte op_prec() { return _t.op_prec(); }

}

