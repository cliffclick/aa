package com.cliffc.aa.node;

import com.cliffc.aa.*;

/** Control flow error nodes.  If any remain in the program after optimization,
 *  the program is not well-typed. */
public final class ErrNode extends Node {
  final String _msg;
  public ErrNode( Node ctrl, String msg ) { super(OP_ERR,ctrl); _msg = msg; }
  @Override String str() { return _msg; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return gvn.type(at(0)); } // Just pass control state thru
  @Override public Type all_type() { return Type.CONTROL; }
  @Override public int hashCode() { return _msg.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ErrNode) ) return false;
    ErrNode err = (ErrNode)o;
    return _msg.equals(err._msg);
  }
}
