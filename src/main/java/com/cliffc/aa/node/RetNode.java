package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class RetNode extends Node {
  public RetNode( Node ctrl, Node ret, Node fun ) { super(OP_RET,ctrl,ret,fun); }
  @Override public Node ideal(GVNGCM gvn) {
    // Test for projnode users; for any funnode input path without a matching
    // projnode user, can whack the funnode input path to ANY.
    long l=0;
    for( Node use : _uses ) {
      assert use instanceof ProjNode;
      int idx=((ProjNode)use)._idx;
      if( idx >= 64 ) throw AA.unimpl();
      l |= (1L<<idx);
    }
    FunNode fun = (FunNode)at(2);
    for( int i=1; i<fun._defs._len; i++ )
      if( (l&(1L<<i))==0 && gvn.type(fun.at(i))!= TypeErr.ANY )
        throw AA.unimpl();      // Whack to ANY; add to worklist
    return null;
  }
  // Builds a CONTROL tuple similar to IfNode
  @Override public Type value(GVNGCM gvn) {
    FunNode fun = (FunNode)at(2);
    Type[] ts = new Type[fun._defs._len];
    ts[0] = TypeErr.ANY; // Slot 0 is not used
    for( int i=1; i<fun._defs._len; i++ )
      ts[i] = gvn.type(fun.at(i));
    return TypeTuple.make(ts);
  }
  @Override public Type all_type() { return TypeTuple.make(TypeErr.CONTROL,false); }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public int op_prec() { return _defs.at(1).op_prec(); }
}
