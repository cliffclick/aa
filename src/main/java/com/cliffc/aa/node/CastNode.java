package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Gain precision after an If-test.
public class CastNode extends Node {
  public final Type _t;                // TypeVar???
  CastNode( Node ctrl, Node ret, Type t ) { super(OP_CAST,ctrl,ret); _t=t; }
  @Override String xstr() { return "("+_t+")"; }
  @Override public Node ideal(GVNGCM gvn) {
    // Cast is useless?  Remove same a TypeNode
    Type c = gvn.type(in(0));
    Type t = gvn.type(in(1));
    return c == Type.CTRL && t.isa(_t) ? in(1) : null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(in(0));
    if( c != Type.CTRL ) return c.above_center() ? Type.ANY : Type.ALL;
    Type t = gvn.type(in(1));
    // CNC - I really badly do not like this, but I don't have a better answer
    // right now.  The case arises when null-check is partially processed in
    // e.g. iter() or opto(), and the guard nil test has not yet dropped to
    // false and the input is a nil to a not-nil cast.  The join lifts high
    // fast, and then goes dead.  The old type was some legit thing, and then
    // e.g. inlining or some other ideal() call triggers a non-monotonic update
    // and the input becomes nil.
    if( t == Type.NIL && _t==Type.NSCALR ) return gvn.self_type(this);
    return _t.join(t);
  }
}
