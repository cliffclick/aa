package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;
import com.cliffc.aa.type.TypeTuple;

// Regain precision after a call.  Calls return some intended value which
// varies by call-site; e.g. map({A->B}, A[]) returns B[] - but the B type
// varies by call-site.  This Cast is used to "up-lift" call return values.
// Calls can ALSO return e.g. some TypeErr.
public class CastNode extends Node {
  public final Type _t;                // TypeVar???
  public CastNode( Node ctrl, Node ret, Type t ) { super(OP_CAST,ctrl,ret); _t=t; }
  @Override String xstr() { return "("+_t+")"; }
  @Override public Node ideal(GVNGCM gvn) {
    // Must keep a cast, even if it useless, if it points to an Epilog.  The
    // Epilog may split (the function may be split) and the callers seperated.
    // The cast funnels the data-uses along one CFG path to this single node,
    // so on a split we can move all these data uses to the old or the new
    // Epilog by just moving the cast.  Once an Epilog can no longer split, we
    // can remove useless casts.
    Node data = in(1);
    if( data instanceof EpilogNode ) {
      // Note that the control-edge cannot go away (since its an up-cast) but
      // the data edge can refine.
      Node x = data.is_copy(gvn,1); // If the Epilog collapses
      return x == null ? null : set_def(1,x,gvn);
    }
    // If the Epilog is collapsed, the data edge will have moved past the
    // Epilog, allowing the code to reach here.  However, we are still
    // up-casting and so cannot go away unless useless - any up-cast has to
    // remain control-guarded.  However, the control may no longer be an
    // e.g. RPCNode, but whatever test gated the RPC in the first place.
    return gvn.type(data).isa(_t) ? data : null;
  }
  @Override public Type value_ne(GVNGCM gvn) {
    Type t0 = gvn.type_ne(in(1));
    assert !(in(1) instanceof EpilogNode);
    //Type t1 = in(1) instanceof EpilogNode ? ((TypeTuple)t0)._ts[1] : t0;
    //if( t1 instanceof TypeErr && !t1.above_center() )
    //  return t1; // Preserve error returns
    //return _t.join(t1);
    return _t.join(t0);
  }
}
