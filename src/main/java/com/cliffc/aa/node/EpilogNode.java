package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Tail end of functions.  Gathers:
// - exit control; function may never exit or may be more than one
// - exit value;
// - RPC - where to jump-to next; the Contiuation
// - The FunNode function header (quickly maps to SESE region header)
public class EpilogNode extends Node {
  public EpilogNode( Node ctrl, Node val, Node rpc, Node fun ) { super(OP_EPI,ctrl,val,rpc,fun); }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t=TypeTuple.make(gvn.type(ctrl()), // Function exits, or not
                          gvn.type(val ()), // Function return value
                          gvn.type(rpc ()), // Caller; the Continuation
                          fun()._tf);       // Function type plus "fidx"
    assert t.is_fun_ptr();
    return t;
  }
  public    Node ctrl() { return          at(0); } // internal function control
  public    Node val () { return          at(1); } // standard exit value
  public    Node rpc () { return          at(2); } // Almost surely a PhiNode merging RPCs
  public FunNode fun () { return (FunNode)at(3); } // Function header
  @Override String xstr() {                        // Self short name
    String name = fun().name();
    return name==null ? "Epilog" : "Epi#"+name;
  } 
  // Return the op_prec of the returned value.  Not sensible except when call
  // on primitives.
  @Override public byte op_prec() { return val().op_prec(); }
}
