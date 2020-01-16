package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Gain precision after an If-test.
public class CastNode extends Node {
  public final Type _t;                // TypeVar???
  public CastNode( Node ctrl, Node ret, Type t ) { super(OP_CAST,ctrl,ret); _t=t; }
  @Override String xstr() { return "("+_t+")"; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // Cast is useless?  Remove same as a TypeNode
    Node ctrl = in(0), addr = in(1);
    Type c = gvn.type(ctrl), t = gvn.type(addr);
    if( c != Type.CTRL ) return null;
    if( t.isa(_t) ) return in(1);

    // Can we hoist control to a higher test?
    Node baseaddr = addr;
    while( baseaddr instanceof CastNode ) baseaddr = baseaddr.in(1);
    final Node fbaseaddr = baseaddr;

    Node tru = ctrl.walk_dom_last(n -> checked(n,fbaseaddr));
    if( tru==null || tru==ctrl ) return null;
    set_def(0,tru,gvn);
    return this;
  }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(in(0));
    if( c != Type.CTRL ) return c.above_center() ? Type.ANY : Type.ALL;
    Type t = gvn.type(in(1));
    if( t.is_forward_ref() ) return Type.SCALAR;
    // CNC - I really badly do not like this, but I don't have a better answer
    // right now.  The case arises when null-check is partially processed in
    // e.g. iter() or opto(), and the guard nil test has not yet dropped to
    // false and the input is a nil to a not-nil cast.  The join lifts high
    // fast, and then goes dead.  The old type was some legit thing, and then
    // e.g. inlining or some other ideal() call triggers a non-monotonic update
    // and the input becomes nil.
    if( t == Type.NIL && _t==Type.NSCALR ) return gvn.self_type(this);

    // If the cast is in-error, we cannot lift.
    if( !checked(in(0),in(1)) ) return t;
    // Lift result.
    return _t.join(t);
  }

  private static boolean checked( Node n, Node addr ) {
    return n instanceof CProjNode && ((CProjNode)n)._idx==1 &&
      n.in(0) instanceof IfNode &&
      n.in(0).in(1) == addr;
  }
}
