package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); }
  @Override String str() { return "If"; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    // If the input is exactly  zero, we can return false: {ANY,CONTROL}
    // If the input is excludes zero, we can return true : {CONTROL,ANY}
    // If the input is excludes both, we can return ANY:   {ANY,ANY}
    // If the input is includes both, we can return both:  {CONTROL,CONTROL}
    if( gvn.type(at(0))==Type.ANY ) return TypeTuple.IF_ANY;
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
}
