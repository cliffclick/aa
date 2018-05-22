package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Regain precision after a call
public class CastNode extends Node {
  private final Type _t;                // TypeVar???
  CastNode( Node ctrl, Node ret, Type t ) { super(OP_CAST,ctrl,ret); _t=t; }
  @Override String xstr() { return "("+_t+")"; }
  @Override public Node ideal(GVNGCM gvn) {
    // The control edge is only used to bound a function body when its being
    // inlined.  Once the function is no longer being treated function-like the
    // control edge can be removed.
    Node progress=null;
    Node ctrl = at(0);
    Node data = at(1);
    if( ctrl != null && (!(ctrl.at(0) instanceof RetNode) || ctrl.at(0).at(1) != data) )
      progress = set_def(0,ctrl=null,gvn);

    // IF there's no control edge and the cast is useless, the whole CastNode
    // can be removed.
    if( ctrl == null && gvn.type(data).isa(_t) )
      return data;

    return progress;
  }
  @Override public Type value(GVNGCM gvn) { return _t.join(gvn.type(at(1))); }
  @Override public Type all_type() { return Type.SCALAR; }
}
