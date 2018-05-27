package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Tail end of functions.  Gathers:
// - exit control; function may never exit or may be more than one
// - exit value;
// - RPC - where to jump-to next; the Continuation
// - The FunNode function header (quickly maps to SESE region header)
public class EpilogNode extends Node {
  public EpilogNode( Node ctrl, Node val, Node rpc, Node fun ) { super(OP_EPI,ctrl,val,rpc,fun); }
  @Override public Node ideal(GVNGCM gvn) {
    if( skip_ctrl(gvn) ) return this;
    gvn.add_work(fun());
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type t=TypeTuple.make(gvn.type(ctrl()), // Function exits, or not
                          gvn.type(val ()), // Function return value
                          gvn.type(rpc ()), // Caller; the Continuation
                          fun()._tf);       // Function type plus "fidx"
    assert t.is_fun_ptr();
    return t;
  }
  // If the return PC is a constant, this is a single-target function and is
  // effectively being inlined on the spot, removing the function head and tail.
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    assert idx==0 || idx==1;
    assert !gvn.type(rpc()).is_con() || fun().callers_known(gvn);
    return gvn.type(rpc()).is_con() ? at(idx) : null;
  }
  
  public    Node ctrl() { return          at(0); } // internal function control
  public    Node val () { return          at(1); } // standard exit value
  public    Node rpc () { return          at(2); } // Almost surely a PhiNode merging RPCs
  public FunNode fun () { return (FunNode)at(3); } // Function header
  @Override String xstr() {                        // Self short name
    String name = fun().name();
    return name==null ? "Epilog" : "Epi#"+name;
  }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns any/top.
  public static Node forward_ref( GVNGCM gvn, String name ) {
    FunNode fun = gvn.init(new FunNode(name));
    return new EpilogNode(fun,gvn.con(TypeErr.ANY),gvn.con(TypeRPC.ALL_CALL),fun);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return at(0)==at(3) && fun()._tf.is_forward_ref(); }

  // 'this' is a forward reference, probably with multiple uses (and no inlined
  // callers).  Passed in the matching function definition, which is brand new
  // and has no uses.  Merge the two.
  public void merge_ref_def( GVNGCM gvn, String tok, EpilogNode def ) {
    FunNode rfun = fun();
    FunNode dfun = def.fun();
    assert rfun._defs._len==1 && rfun.at(0)==null; // Forward ref has no callers
    assert dfun._defs._len==2 && dfun.at(0)==null && dfun.at(1) instanceof ScopeNode;
    assert def._uses._len==0;                      // Def is brand new, no uses

    gvn.subsume(this,def);
    dfun.bind(tok);
  }

  @Override public Type all_type() { return TypeTuple.GENERIC_FUN; }
  
  // Return the op_prec of the returned value.  Not sensible except when call
  // on primitives.
  @Override public byte op_prec() { return val().op_prec(); }
}
