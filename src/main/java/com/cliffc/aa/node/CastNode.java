package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

// Gain precision after an If-test.
public class CastNode extends Node {
  public final Type _t;                // TypeVar???
  public CastNode( Node ctrl, Node ret, Type t ) { super(OP_CAST,ctrl,ret); _t=t; }
  @Override public String xstr() { return "("+_t+")"; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    Node cc = in(0).is_copy(0);
    if( cc!=null ) return set_def(0,cc,gvn);
    // Cast is useless?  Remove same as a TypeNode
    Node ctrl = in(0), addr = in(1);
    Type c = ctrl.val(), t = addr.val();
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
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type c = val(0);
    if( c != Type.CTRL ) return c.oob();
    Type t = val(1);
    if( t.is_forward_ref() ) return Type.SCALAR;

    // If the cast is in-error, we cannot lift.
    if( !checked(in(0),in(1)) ) return t;
    // Lift result.
    return _t.join(t);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==in(0) ? TypeMem.ALIVE : _live;
  }

  private static boolean checked( Node n, Node addr ) {
    if( !(n instanceof CProjNode && ((CProjNode)n)._idx==1) ) return false; // Not a Cast of a CProj-True
    Node n0 = n.in(0);
    if( n0 instanceof IfNode && n0.in(1) == addr ) return true; // Guarded by If-n-zero
    if( n0 instanceof ConNode && ((TypeTuple) n0.val()).at(1)==Type.XCTRL )
      return true;
    return false;
  }
}
