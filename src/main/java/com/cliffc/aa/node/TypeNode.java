package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Assert the matching type.  Parse-time error if it does not remove.  Note the
// difference with CastNode: both Nodes always join their input with their
// constant but a TypeNode has to be proven useless and removed before the
// program is type-correct.  A CastNode is always correct from call/return
// semantics, but the join is not-locally-obviously-correct.  The Cast makes it
// locally obvious.
public class TypeNode extends Node {
  final Type _t;                // TypeVar???
  final String _msg;
  public TypeNode( Type t, Node n, String msg ) { super(OP_TYPE,null,n); _t=t; _msg = msg; }
  @Override String str() { return "@"+_t; }
  @Override public Node ideal(GVNGCM gvn) {
    Type t = gvn.type(at(1));
    return t.isa(_t) ? at(1) : null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(at(1));
    // Return type is an error, until the assert can be proven and removed.  
    return (t instanceof TypeErr || t.isa(_t)) ? t : TypeErr.make(err(gvn));
    // Cannot return a join, because the upcast type will propagate far and
    // wide and allow an upcast function type to inline.
    //return _t.join(t);
  }
  @Override public Type all_type() { return _t; }
  String err(GVNGCM gvn) {
    return String.format(_msg,gvn.type(at(1)).toString()+" is not a "+_t);
  }
}
