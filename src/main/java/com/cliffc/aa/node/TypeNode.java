package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Assert the matching type.  Parse-time error if it does not remove.
public class TypeNode extends Node {
  private final Type _t;                // TypeVar???
  private final String _msg;
  public TypeNode( Type t, Node n, String msg ) { super(OP_TYPE,null,n); _t=t; _msg = msg; }
  @Override String str() { return "@"+_t; }
  @Override public Node ideal(GVNGCM gvn) {
    Type t = gvn.type(at(1));
    return !(t instanceof TypeErr) && t.isa(_t) ? at(1) : null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(at(1));
    // Return type is an error, until the assert can be proven and removed.  
    return (t instanceof TypeErr || t.isa(_t)) ? t : TypeErr.make(err(gvn));
  }
  @Override public Type all_type() { return TypeErr.ALL; }
  String err(GVNGCM gvn) {
    return String.format(_msg,gvn.type(at(1)).toString()+" is not a "+_t);
  }
}
