package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); }
  @Override String str() { return "If"; }
  @Override public Node ideal(GVNGCM gvn) {
    if( skip_ctrl(gvn) ) return this;
    return null;
  }
  @Override public TypeTuple value(GVNGCM gvn) {
    // If the input is exactly  zero, we can return false: {ANY,CONTROL}
    // If the input is excludes zero, we can return true : {CONTROL,ANY}
    // If the input is excludes both, we can return ANY:   {ANY,ANY}
    // If the input is includes both, we can return both:  {CONTROL,CONTROL}
    if( gvn.type(at(0))==TypeErr.ANY ) return TypeTuple.IF_ANY;
    Type pred = gvn.type(at(1));
    if( pred.isa(TypeInt.XINT1) ) return TypeTuple.IF_ANY;
    if( TypeInt.BOOL.isa(pred)  ) return TypeTuple.IF_ALL;
    if( pred==TypeInt.FALSE     ) return TypeTuple.IF_FALSE;
    if( !(pred instanceof TypeInt) )
      throw AA.unimpl();
    if( pred.is_con() ) { assert pred.getl() != 0; return TypeTuple.IF_TRUE; }
    return TypeTuple.IF_ANY;    // No more refinement than constant 0 vs constant non-zero
  }
  @Override public Type all_type() { return TypeTuple.IF_ALL; }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    TypeTuple tt = (TypeTuple)gvn.type(at(0));
    assert tt._inf==TypeErr.ANY;
    if( tt==TypeTuple.IF_TRUE  && idx==1 ) return at(0).at(0);
    if( tt==TypeTuple.IF_FALSE && idx==0 ) return at(0).at(0);
    return null;
  }
}
