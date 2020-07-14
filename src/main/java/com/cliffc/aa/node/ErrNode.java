package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

/** Error nodes.  If any remain in the program after optimization, the program
 *  is not well-typed. */
public final class ErrNode extends Node {
  final String _msg;            // Error message
  final Parse _bad;             // Optional open point for missing close
  public ErrNode( Node ctrl, String msg, Parse bad ) { super(OP_ERR,ctrl); _msg = msg; _bad = bad; _live= TypeMem.ESCAPE; }
  @Override String xstr() { return _msg.split("\n")[1]; }
  @Override String str() { return "Err"; }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(0));
    return t == Type.ANY || t == Type.XCTRL ? Type.ANY : Type.ALL; // For dead data errors return ANY (no error)
  }
  @Override public String err(GVNGCM gvn) {
    return _bad == null ? _msg : _msg + _bad.errMsg("Missing close was opened here");
  }
  @Override public int hashCode() { return super.hashCode()+_msg.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ErrNode) ) return false;
    ErrNode err = (ErrNode)o;
    return _msg.equals(err._msg);
  }
}
