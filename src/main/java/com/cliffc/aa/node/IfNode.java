package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

// Split control
public class IfNode extends Node {
  public IfNode( Node ctrl, Node pred ) { super(OP_IF,ctrl,pred); }
  
  @Override boolean is_CFG() { return is_copy(0)==null; }

  @Override public Node ideal_reduce() {
    if( is_prim() ) return null;
    Node cc = fold_ccopy();
    if( cc!=null ) return cc;
    Node ctl = in(0);
    Node tst = in(1);
    if( ctl._val == Type.XCTRL && tst!=Env.ANY )
      return set_def(1,Env.ANY); // Kill test; control projections fold up other ways
    else ctl.deps_add(this);
    
    // Binary test vs 0?
    if( tst._defs._len==3 &&
        (tst.val(1)==TypeNil.NIL || tst.val(2)==TypeNil.NIL) ) {
      // Remove leading test-vs-0
      if( tst instanceof PrimNode.EQ_I64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.EQ_F64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.EQ_OOP ) throw AA.unimpl();

      // Remove leading negation-vs-0 by inverting
      if( tst instanceof PrimNode.NE_I64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.NE_F64 ) throw AA.unimpl();
      if( tst instanceof PrimNode.NE_OOP ) throw AA.unimpl();
    }

    if( tst instanceof PrimNode.NotI64 && tst._uses._len==1 )
      //return flip(Env.GVN.xreduce(new IfNode(ctl,tst.in(ARG_IDX))));
      throw unimpl();

    return null;
  }
  Node flip(Node that) {
    ProjNode p0 = (ProjNode)_uses.atX(0);
    ProjNode p1 = (ProjNode)_uses.atX(1);
    if( p0==null || p1==null ) return null; // Not well-formed
    if( p0._idx==1 ) { ProjNode tmp=p0; p0=p1; p1=tmp; }
    //Node x0 = Env.GVN.xreduce(new CProjNode(that,0));
    //Node x1 = Env.GVN.xreduce(new CProjNode(that,1));
    //p0.subsume(x1);
    //p1.subsume(x0);
    //x0._live = x1._live = that._live = this._live;
    //return that;
    throw unimpl();
  }

  @Override public TypeTuple value() {
    // If the input is exactly zero, we can return false: {ANY,CONTROL}
    // If the input excludes   zero, we can return true : {CONTROL,ANY}
    // If the input excludes   both, we can return ANY:   {ANY,ANY}
    // If the input includes   both, we can return both:  {CONTROL,CONTROL}
    Type ctrl = val(0);
    if( ctrl.above_center() ) return TypeTuple.IF_ANY; // Test is dead
    if( in(0) instanceof ProjNode && in(0).in(0)==this )
      return TypeTuple.IF_ANY; // Test is dead cycle of self (during collapse of dead loops)
    Type pred = val(1);
    return truthy(pred);
  }

  // Returns
  //   TypeTuple.IF_FALSE - If always nil, 0:int, 0:flt
  //   TypeTuple.IF_TRUE  - If nil never appears
  //   TypeTuple.IF_ALL   - If cannot tell true or false
  //   TypeTuple.IF_ANY   - If cannot be either true or false
  public static TypeTuple truthy(Type pred) {
    // Handle predicates, especially XNIL and wrapped ints (TypeStruct with
    // perhaps constant fields).
    if( pred == TypeNil.NIL    ) return TypeTuple.IF_FALSE; // The One True Zero
    if( pred == TypeInt.ZERO   ) return TypeTuple.IF_FALSE; // 
    if( pred == TypeFlt.con(0) ) return TypeTuple.IF_FALSE; //
    if( pred == TypeNil.XSCALAR) return TypeTuple.IF_ANY;   // TODO: cleanup
    if( pred == Type.ANY       ) return TypeTuple.IF_ANY;   // TODO: cleanup
    if( !TypeNil.NIL.isa(pred) ) return TypeTuple.IF_TRUE;  // missing zero, so TRUE

    // Handle e.g. TMP and TFP nil checks
    if( !(pred instanceof TypeNil tn) ) return (TypeTuple)pred.oob(TypeTuple.IF_ALL);
    if( tn._nil ) return tn._sub ? TypeTuple.IF_ANY  : TypeTuple.IF_FALSE;
    else          return tn._sub ? TypeTuple.IF_TRUE : TypeTuple.IF_ALL;
  }

  @Override public boolean has_tvar() { return false; }

  @Override public Node is_copy(int idx) {
    if( is_prim() ) return null;
    if( !(_val instanceof TypeTuple tt) ) return null;
    if( tt.above_center() ) return Env.XCTRL;
    if( tt==TypeTuple.IF_TRUE  && idx==1 ) return in(0);
    if( tt==TypeTuple.IF_FALSE && idx==0 ) return in(0);
    Node proj = ProjNode.proj(this,idx);
    if( proj!=null ) deps_add(proj);
    return null;
  }
}
