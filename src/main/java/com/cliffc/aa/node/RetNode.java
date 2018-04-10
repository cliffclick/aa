package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class RetNode extends Node {
  final int _rpc;               // Which call site
  public RetNode( Node ctrl, Node ret, Node rpcparm, int rpc ) { super(OP_RET,ctrl,ret,rpcparm); _rpc = rpc;}
  @Override String str() { return "ret$"+_rpc; }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  // RetNodes *are* the function pointers, as opposed to FunNodes.  Thus their
  // type is that of a function, not of what is being returned.
  @Override public Type value(GVNGCP gvn) { return gvn.type(at(2).at(0)); }
  @Override public Type all_type() { return Type.SCALAR; }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public int op_prec() { return _defs.at(1).op_prec(); }
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof RetNode) ) return false;
    RetNode ret = (RetNode)o;
    return _rpc==ret._rpc;
  }
}
