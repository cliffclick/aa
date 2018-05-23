package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Regain precision after a call
public class CastNode extends Node {
  private final Type _t;                // TypeVar???
  CastNode( Node ctrl, Node ret, Type t ) { super(OP_CAST,ctrl,ret); _t=t; }
  @Override String xstr() { return "("+_t+")"; }
  @Override public Node ideal(GVNGCM gvn) {
    Node x = at(0).is_copy(gvn,0);
    if( x!=null ) return set_def(0,x,gvn);
    // Must keep a cast, even if it useless, if it points to an Epilog.  The
    // Epilog may split (the function may be split) and the callers seperated.
    // The cast funnels the data-uses along one CFG path to this single node,
    // so on a split we can move all these data uses to the old or the new
    // Epilog by just moving the cast.  Once an Epilog can no longer split the
    // cast will lose its control edge, and useless casts can then be removed.
    if( at(0) instanceof RPCNode && at(0).at(0) instanceof EpilogNode ) return null;
    return gvn.type(at(1)).isa(_t) ? at(1) : null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type t0 = gvn.type(at(1));
    Type t1 = at(1) instanceof EpilogNode ? ((TypeTuple)t0)._ts[1] : t0;
    return _t.join(t1);
  }
  @Override public Type all_type() { return Type.SCALAR; }
}
