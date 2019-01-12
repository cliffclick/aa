package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;

/** Error nodes.  If any remain in the program after optimization, the program
 *  is not well-typed. */
public final class ErrNode extends Node {
  final String _msg;            // Error message
  public final Type _t;         // Default value if no error
  public ErrNode( Node ctrl, String msg, Type t ) { super(OP_ERR,ctrl); _msg = msg; _t=t; }
  @Override String xstr() { return _msg; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(0));
    if( _t == Type.CTRL ) return t; // For control errors, pass through incoming control
    return t == Type.ANY || t == Type.XCTRL ? Type.ANY : _t; // For dead data errors return ANY (no error)
  }
  @Override public String err(GVNGCM gvn) { return _msg; }
  @Override public Type all_type() { return _t; }
  @Override public int hashCode() { return super.hashCode()+_msg.hashCode()+_t.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ErrNode) ) return false;
    ErrNode err = (ErrNode)o;
    return _msg.equals(err._msg) && _t==err._t;
  }
}
