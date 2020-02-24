package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;

// Proj data
public class ProjNode extends Node {
  final int _idx;
  public ProjNode( Node ifn, int idx ) { this(OP_PROJ,ifn,idx); }
  ProjNode( byte op, Node ifn, int idx ) { super(op,ifn); _idx=idx; }
  @Override String xstr() { return "DProj_"+_idx; }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // multi-head is collapsing?  Then follow suit.
    Node cp = in(0).is_copy(gvn,_idx);
    if( cp != null ) return cp;

    // Basic escape analysis if DProj loses a use
    if( in(0) instanceof NewNode && ((NewNode) in(0)).captured(gvn) )
      gvn.add_work(in(0));

    return null;
  }

  // If losing an escaping use, recheck escape analysis
  @Override public boolean ideal_impacted_by_losing_uses(GVNGCM gvn, Node dead) {
    return
      dead instanceof  CallNode || // Call args escape
      dead instanceof  LoadNode || // Direct usage
      dead instanceof StoreNode;   // Store this-as-val escapes
  }

  @Override public Type value(GVNGCM gvn) {
    if( in(0) instanceof NewNode && ((NewNode)in(0))._captured )
      return Type.XSCALAR;
    Type c = gvn.type(in(0));
    if( c instanceof TypeTuple ) {
      TypeTuple ct = (TypeTuple)c;
      if( _idx < ct._ts.length ) {
        Type t = ct._ts[_idx].meet(Type.XSCALAR);
        return Type.SCALAR.isa(t) ? Type.SCALAR : t;
      }
    }
    return c.above_center() ? Type.XSCALAR : Type.SCALAR;
  }
  @Override public Type all_type() { return Type.SCALAR; }

  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ProjNode) ) return false;
    ProjNode proj = (ProjNode)o;
    return _idx==proj._idx;
  }
}
