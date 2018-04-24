package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class RetNode extends Node {
  public RetNode( Node ctrl, Node ret, Node fun ) { super(OP_RET,ctrl,ret,fun); }
  @Override public Node ideal(GVNGCM gvn) {
    return null;
  }
  // Builds a CONTROL tuple similar to IfNode
  @Override public Type value(GVNGCM gvn) {
    FunNode fun = (FunNode)at(2);
    Type[] ts = new Type[fun._defs._len];
    ts[0] = TypeErr.ANY; // Slot 0 is not used, slot 1 is the unknown control
    for( int i=1; i<fun._defs._len; i++ )
      ts[i] = gvn.type(fun.at(i));
    return TypeTuple.make(TypeErr.CONTROL,false,ts);
  }
  @Override public Type all_type() { return TypeTuple.make(TypeErr.CONTROL,false); }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public int op_prec() { return _defs.at(1).op_prec(); }
}
