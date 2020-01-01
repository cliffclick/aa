package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); }
  @Override public Node ideal(GVNGCM gvn) {
    return gvn.type(in(0)) == Type.XCTRL ? gvn.con(TypeTuple.IF_ANY) : null;
  }
  @Override public TypeTuple value(GVNGCM gvn) {
    // If the input is exactly zero, we can return false: {ANY,CONTROL}
    // If the input excludes   zero, we can return true : {CONTROL,ANY}
    // If the input excludes   both, we can return ANY:   {ANY,ANY}
    // If the input includes   both, we can return both:  {CONTROL,CONTROL}
    Type ctrl = gvn.type(in(0));
    if( ctrl!=Type.CTRL && ctrl != Type.ALL ) return TypeTuple.IF_ANY; // Test is dead
    if( in(0) instanceof ProjNode && in(0).in(0)==this )
      return TypeTuple.IF_ANY; // Test is dead cycle of self (during collapse of dead loops)
    Type pred = gvn.type(in(1));
    if( pred instanceof TypeTuple)return TypeTuple.IF_ANY;// Nonsense, so test is dead
    if( pred instanceof TypeObj ) return TypeTuple.IF_ANY;// Nonsense, so test is dead
    if( pred.isa(TypeInt.XINT1) ) return TypeTuple.IF_ANY; // Choice of {0,1}
    if( TypeInt.BOOL.isa(pred)  ) return TypeTuple.IF_ALL; // Can be either
    if( pred == TypeInt.FALSE || pred == Type.NIL )
      return TypeTuple.IF_FALSE;   // False only
    
    // Already checked for exactly NIL.
    // If pred maybe a nil, then we can choose nil or something else
    if( pred. may_nil() ) return TypeTuple.IF_ANY;
    // If pred must include a nil, then we can see nil or something else
    if( pred.must_nil() ) return TypeTuple.IF_ALL;
    // Let input fall before deciding
    if( pred.above_center() ) return TypeTuple.IF_ANY;
    // If meeting a nil changes things, then the original excluded nil and so
    // was always true.
    if( pred.meet_nil() != pred ) return TypeTuple.IF_TRUE;
    
    throw AA.unimpl(); // Dunno what test this is?
  }
  @Override public Type all_type() { return TypeTuple.IF_ALL; }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    TypeTuple tt = (TypeTuple)gvn.type(this);
    if( tt==TypeTuple.IF_ANY ) return gvn.con(Type.XCTRL);
    if( tt==TypeTuple.IF_TRUE  && idx==1 ) return in(0);
    if( tt==TypeTuple.IF_FALSE && idx==0 ) return in(0);
    return null;
  }
}
