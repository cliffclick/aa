package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); }

  @Override public Node ideal_reduce() {
    Node ctl = in(0);
    Node tst = in(1);
    if( ctl._val == Type.XCTRL && in(1)!=Env.ANY )
      return set_def(1,Env.ANY); // Kill test; control projections fold up other ways
    // Binary test vs 0?
    if( tst._defs._len==3 &&
        (tst.val(1)==Type.XNIL || tst.val(2)==Type.XNIL) ) {
      // Remove leading test-vs-0
      if( tst instanceof PrimNode.EQ_I64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.EQ_F64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.EQ_OOP ) throw AA.unimpl();

      // Remove leading negation-vs-0 by inverting
      if( tst instanceof PrimNode.NE_I64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.NE_F64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.NE_OOP ) throw AA.unimpl();
    }

    if( tst instanceof PrimNode.Not && tst._uses._len==1 )
      return flip(Env.GVN.xreduce(new IfNode(ctl,tst.in(1))));

    return null;
  }
  Node flip(Node that) {
    ProjNode p0 = (ProjNode)_uses.atX(0);
    ProjNode p1 = (ProjNode)_uses.atX(1);
    if( p0==null || p0._keep>0 || p1==null || p1._keep>0 ) return null; // Not well formed
    if( p0._idx==1 ) { ProjNode tmp=p0; p0=p1; p1=tmp; }
    Node x0 = Env.GVN.xreduce(new CProjNode(that,0));
    Node x1 = Env.GVN.xreduce(new CProjNode(that,1));
    p0.subsume(x1);
    p1.subsume(x0);
    x0._live = x1._live = that._live = this._live;
    return that;
  }


  @Override public TypeTuple value(GVNGCM.Mode opt_mode) {
    // If the input is exactly zero, we can return false: {ANY,CONTROL}
    // If the input excludes   zero, we can return true : {CONTROL,ANY}
    // If the input excludes   both, we can return ANY:   {ANY,ANY}
    // If the input includes   both, we can return both:  {CONTROL,CONTROL}
    Type ctrl = val(0);
    if( ctrl!=Type.CTRL && ctrl != Type.ALL ) return TypeTuple.IF_ANY; // Test is dead
    if( in(0) instanceof ProjNode && in(0).in(0)==this )
      return TypeTuple.IF_ANY; // Test is dead cycle of self (during collapse of dead loops)
    Type pred = val(1);
    if( pred instanceof TypeTuple)return TypeTuple.IF_ANY;// Nonsense, so test is dead
    if( pred instanceof TypeObj ) return TypeTuple.IF_ANY;// Nonsense, so test is dead
    if( pred.isa(TypeInt.INT1.dual()) ) return TypeTuple.IF_ANY; // Choice of {0,1}
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
  @Override public TypeMem all_live() { return TypeMem.ALIVE; }

  @Override public TV2 new_tvar(String alloc_site) { return TV2.make("If",this,alloc_site); }

  @Override public Node is_copy(int idx) {
    if( !(_val instanceof TypeTuple) ) return null;
    TypeTuple tt = (TypeTuple) _val;
    if( tt==TypeTuple.IF_ANY ) return Env.XCTRL;
    if( tt==TypeTuple.IF_TRUE  && idx==1 ) return in(0);
    if( tt==TypeTuple.IF_FALSE && idx==0 ) return in(0);
    return null;
  }
}
