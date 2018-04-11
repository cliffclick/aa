package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class RetNode extends Node {
  final int _rpc;               // Which call site
  public RetNode( Node ctrl, Node ret, Node rpcparm, int rpc ) { super(OP_RET,ctrl,ret,rpcparm); _rpc = rpc;}
  @Override String str() { return "ret$"+_rpc; }
  @Override public Node ideal(GVNGCP gvn) {
    if( _rpc==1 ) return null; // Do not muck with the unknown caller
    // special case: function body is a single node (e.g. a primitive).
    // Inline immediately.  Pattern is:
    // all  X  all  arg   1  rpc
    //   fun    parm      parm
    //       op_points_to_multiple_parms
    //        ret
    Node ctrl = _defs.at(0);    // probably null
    Node op   = _defs.at(1);
    Node rpc  = _defs.at(2);
    Node fun  = rpc._defs.at(0);
    // All args to op come from function header
    for( Node parm : op._defs )
      if( parm!=null && parm._defs.at(0) != fun )
        return null;
    // Find the call-site specific incoming path
    int idx;
    for( idx=1; idx<rpc._defs._len; idx++ )
      if( gvn.type(rpc._defs.at(idx)).getl() == _rpc )
        break;
    assert idx < rpc._defs._len;
    // Inline the function body (a single op)
    Node nnn = op.copy();       // A copy, no use/def
    for( Node parm : op._defs ) { // Copy edges
      Node x = parm == null ? null : parm._defs.at(idx);
      nnn.add_def(x);
    }
    return nnn;
  }
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
