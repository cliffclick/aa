package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;

// See CallNode comments.  The RetNode which gathers {control (function exits
// or not), memory, value, rpc}, and sits at the end of a function just prior
// to the EpilogNode.
public final class RetNode extends Node {
  public RetNode( Node ctrl, Node mem, Node val, Node rpc ) { super(OP_RET,ctrl,mem,val,rpc); }
  public Node ctl() { return in(0); }
  public Node mem() { return in(1); }
  public Node val() { return in(2); }
  public Node rpc() { return in(3); }
  
  @Override public Node ideal(GVNGCM gvn) {
    if( _uses._len >0 ) { // ignore parsing startup
      if( in(1)==null ) return null; // Already stripped
      // Should be used by exactly one Epilog, plus some CallEpis.  If no Epilog,
      // then the function inlined, the Epilog inlined and this should too.
      for( Node use : _uses )
        if( use instanceof EpilogNode && use.is_copy(gvn,0)==null )
          return null;
      // Strip off input edges, all dead now
      //for( int i=1; i<_defs._len; i++ ) set_def(i,null,gvn);
      //return this;
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    return TypeTuple.make(gvn.type(ctl()),gvn.type(mem()),gvn.type(val()));
  }
  @Override public Type all_type() { return TypeTuple.CALL; }
}
