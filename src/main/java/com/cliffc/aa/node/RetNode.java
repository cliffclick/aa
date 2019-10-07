package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

// See CallNode comments.  The RetNode gathers {control (function exits or
// not), memory, value, rpc, fun}, and sits at the end of a function.  The RPC
// dictates which calls can be reached from here.  The Fun is used to rapidly
// find the FunNode, as a SESE region shortcut.  A FunPtrNode points to this
// Ret, and is used for all function-pointer uses.  Otherwise only CallEpis
// point to a Ret representing wired calls.

public final class RetNode extends Node {
  int _fidx;                    // Shortcut to fidx when the FunNode has collapsed
  public RetNode( Node ctrl, Node mem, Node val, Node rpc, FunNode fun ) { super(OP_RET,ctrl,mem,val,rpc,fun); _fidx = fun.fidx();}
  public Node ctl() { return in(0); }
  public Node mem() { return in(1); }
  public Node val() { return in(2); }
  public Node rpc() { return in(3); }
  public FunNode fun() { return (FunNode)in(4); }
  public FunPtrNode funptr() {
    for( Node use : _uses )
      if( use instanceof FunPtrNode )
        return (FunPtrNode)use;
    return null;
  }
  public int fidx() { return _fidx; }
  // Short self name
  @Override String xstr() {
    if( is_dead() ) return "Ret";
    FunNode fun = FunNode.find_fidx(_fidx);
    return "Ret_"+(is_copy() ? "!copy!" : (fun==null ? ""+_fidx : fun.name()));
  }
  // Inline longer name
  @Override public String str() { return in(4) instanceof FunNode ? "Ret"+fun().str() : xstr(); }

  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type ctl = gvn.type(ctl()).bound(Type.CTRL);
    Type mem = gvn.type(mem()).bound(TypeMem.MEM);
    Type val = gvn.type(val()).bound(Type.SCALAR);
    return TypeTuple.make(ctl,mem,val);
  }
  @Override public Type all_type() { return TypeTuple.CALL; }

  @Override public Node is_copy(GVNGCM gvn, int idx) { throw com.cliffc.aa.AA.unimpl(); }
  boolean is_copy() { return !(in(4) instanceof FunNode) || fun()._tf.fidx() != _fidx; }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() {
    return val()._uid < GVNGCM._INIT0_CNT ? val().op_prec() : -1;
  }

  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }
}
