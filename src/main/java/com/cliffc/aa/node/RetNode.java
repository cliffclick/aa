package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class RetNode extends Node {
  final int _rpc;               // Which call site
  public RetNode( Node ctrl, Node ret, Node rpcparm, int rpc ) { super(OP_RET,ctrl,ret,rpcparm); _rpc = rpc;}
  @Override String str() { return "ret$"+_rpc; }
  @Override public Node ideal(GVNGCP gvn) {
    if( _rpc==1 ) return null;  // Generic worse-case caller
    // Which call site
    throw AA.unimpl();
  }
  // RetNodes *are* the function pointers, as opposed to FunNodes.  Thus their
  // type is that of a function.
  @Override public Type value(GVNGCP gvn) { return gvn.type(at(2).at(0));  }
  @Override public Type all_type() { return Type.SCALAR; }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public int op_prec() { return _defs.at(1).op_prec(); }
}
