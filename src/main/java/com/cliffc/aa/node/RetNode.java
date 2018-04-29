package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class RetNode extends Node {
  public RetNode( Node ctrl, Node ret, Node fun ) { super(OP_RET,ctrl,ret,fun); }
  @Override public Node ideal(GVNGCM gvn) {

    // Look for missing ProjNodes, meaning a dead-path into the function
    long l=0;
    for( Node proj : _uses )
      if( proj instanceof ProjNode ) {
        int idx = ((ProjNode)proj)._idx;
        assert idx < 64;
        l |= (1L<<idx);
      }

    Node fun = at(2);
    for( int i=1; i<fun._defs._len; i++ ) {
      if( (l & (1L<<i))==0 ) {
        gvn.unreg(fun);
        fun.set_def(i,gvn.con(TypeErr.ANY),gvn);
        gvn.rereg(fun);
      }
    }
    
    return null;
  }
  // Builds a CONTROL tuple similar to IfNode
  @Override public Type value(GVNGCM gvn) {
    FunNode fun = (FunNode)at(2);
    Type[] ts = new Type[fun._defs._len];
    ts[0] = TypeErr.ANY; // Slot 0 is not used, slot 1 is the unknown control
    for( int i=1; i<fun._defs._len; i++ )
      ts[i] = gvn.type(fun.at(i));
    return TypeTuple.make(TypeErr.CONTROL,1.0,ts);
  }
  @Override public Type all_type() { return TypeTuple.make(TypeErr.CONTROL,1.0); }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.  Queries the Fun, not the primitive.
  @Override public byte op_prec() { return _defs.at(2).op_prec(); }
}
