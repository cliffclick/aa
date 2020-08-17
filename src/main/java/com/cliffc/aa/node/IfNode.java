package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); _live=TypeMem.ALIVE; }
  @Override public Node ideal(GVNGCM gvn, int level) {
    Node ctl = in(0);
    Node tst = in(1);
    if( ctl._val == Type.XCTRL ) return gvn.con(TypeTuple.IF_ANY);
    // Binary test vs 0?
    if( tst._defs._len==3 &&
        (tst.in(1)._val==Type.XNIL || tst.in(2)._val==Type.XNIL) ) {
      // Remove leading test-vs-0
      if( tst instanceof PrimNode.EQ_I64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.EQ_F64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.EQ_OOP ) throw AA.unimpl();
    
      // Remove leading negation-vs-0 by inverting
      if( tst instanceof PrimNode.NE_I64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.NE_F64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.NE_OOP ) throw AA.unimpl();
    }
    
    if( tst instanceof PrimNode.Not ) return flip(gvn, gvn.xform(new IfNode(ctl,tst.in(1))));
    
    return null;
  }

  Node flip(GVNGCM gvn, Node that) {
    ProjNode p0 = (ProjNode)_uses.atX(0);
    ProjNode p1 = (ProjNode)_uses.atX(1);
    if( p0!=null && p0._idx==1 ) { ProjNode tmp=p0; p0=p1; p1=tmp; }
    Node x0 = gvn.xform(new CProjNode(that,0));
    Node x1 = gvn.xform(new CProjNode(that,1));
    if( p0!=null ) gvn.replace(p0,x1);
    if( p1!=null ) gvn.replace(p1,x0);
    return that;
  }

  
  @Override public TypeTuple value(byte opt_mode) {
    // If the input is exactly zero, we can return false: {ANY,CONTROL}
    // If the input excludes   zero, we can return true : {CONTROL,ANY}
    // If the input excludes   both, we can return ANY:   {ANY,ANY}
    // If the input includes   both, we can return both:  {CONTROL,CONTROL}
    Type ctrl = in(0)._val;
    if( ctrl!=Type.CTRL && ctrl != Type.ALL ) return TypeTuple.IF_ANY; // Test is dead
    if( in(0) instanceof ProjNode && in(0).in(0)==this )
      return TypeTuple.IF_ANY; // Test is dead cycle of self (during collapse of dead loops)
    Type pred = in(1)._val;
    if( pred instanceof TypeTuple)return TypeTuple.IF_ANY;// Nonsense, so test is dead
    if( pred instanceof TypeObj ) return TypeTuple.IF_ANY;// Nonsense, so test is dead
    if( pred.isa(TypeInt.XINT1) ) return TypeTuple.IF_ANY; // Choice of {0,1}
    if( TypeInt.BOOL.isa(pred)  ) return TypeTuple.IF_ALL; // Can be either
    if( pred == TypeInt.FALSE || pred == Type.NIL || pred==Type.XNIL )
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
    if( pred.meet_nil(Type.NIL) != pred ) return TypeTuple.IF_TRUE;

    throw AA.unimpl(); // Dunno what test this is?
  }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    if( !(_val instanceof TypeTuple) ) return null;
    TypeTuple tt = (TypeTuple)_val;
    if( tt==TypeTuple.IF_ANY ) return gvn.con(Type.XCTRL);
    if( tt==TypeTuple.IF_TRUE  && idx==1 ) return in(0);
    if( tt==TypeTuple.IF_FALSE && idx==0 ) return in(0);
    return null;
  }
}
