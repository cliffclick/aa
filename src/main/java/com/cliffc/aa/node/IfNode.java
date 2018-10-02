package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public TypeTuple value(GVNGCM gvn) {
    // If the input is exactly zero, we can return false: {ANY,CONTROL}
    // If the input excludes   zero, we can return true : {CONTROL,ANY}
    // If the input excludes   both, we can return ANY:   {ANY,ANY}
    // If the input includes   both, we can return both:  {CONTROL,CONTROL}
    if( gvn.type(in(0))==Type.XCTRL ) return TypeTuple.IF_ANY; // Test is dead
    if( in(0) instanceof ProjNode && in(0).in(0)==this )
      return TypeTuple.IF_ANY; // Test is dead cycle of self (during collapse of dead loops)
    Type pred = gvn.type(in(1));
    if( pred.isa(TypeInt.XINT1) ) return TypeTuple.IF_ANY;  // Choice of {0,1}
    if( TypeInt.BOOL.isa(pred)  ) return TypeTuple.IF_ALL;  // Can be either
    if( pred.isa(TypeInt.FALSE) ) return TypeTuple.IF_FALSE;// False only
    if( pred instanceof TypeNullable ) {
      switch( ((TypeNullable)pred)._nil ) {
      case TypeNullable. IS_NIL: return TypeTuple.IF_FALSE;
      case TypeNullable.NOT_NIL: return TypeTuple.IF_TRUE;
      case TypeNullable.AND_NIL: return TypeTuple.IF_ALL;   // Might be nil or the oop
      case TypeNullable. OR_NIL: return TypeTuple.IF_FALSE; // Take nil choice
      }
    }
    if( !(pred instanceof TypeInt) )
      throw AA.unimpl(); // Dunno what this test is?
    if( pred.is_con() ) { assert pred.getl() != 0; return TypeTuple.IF_TRUE; } // True only
    throw AA.unimpl(); // Dunno what this test is?
  }
  @Override public Type all_type() { return TypeTuple.IF_ALL; }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    TypeTuple tt = (TypeTuple)gvn.type(this);
    assert tt._inf==Type.ALL;
    if( tt==TypeTuple.IF_TRUE  && idx==1 ) return in(0);
    if( tt==TypeTuple.IF_FALSE && idx==0 ) return in(0);
    return null;
  }
}
