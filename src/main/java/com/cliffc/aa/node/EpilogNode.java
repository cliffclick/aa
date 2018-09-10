package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Tail end of functions.  Gathers:
// - exit control; function may never exit or may be more than one
// - exit value;
// - RPC - where to jump-to next; the Continuation
// - The FunNode function header (quickly maps to SESE region header)
public class EpilogNode extends Node {
  private final int _fidx;
  final String _unkref_err; // Unknown ref error (not really a forward ref)
  public EpilogNode( Node ctrl, Node val, Node rpc, FunNode fun, String unkref_err ) {
    super(OP_EPI,ctrl,val,rpc,fun);
    _unkref_err = unkref_err;
    _fidx = fun._tf.fidx();     // Record function index, so can tell it exactly
  }
  @Override public Node ideal(GVNGCM gvn) { return null; }

  @Override public Type value(GVNGCM gvn) {
    Type t=TypeTuple.make_all(gvn.type(ctrl()), // Function exits, or not
                              gvn.type(val ()), // Function return value
                              gvn.type(rpc ()), // Caller; the Continuation
                              FunNode.find_fidx(_fidx)._tf);
    assert t.is_fun_ptr();
    return t;
  }
  @Override public String err(GVNGCM gvn) { return is_forward_ref() ? _unkref_err : null; }
  
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    return (in(3) instanceof FunNode && ((FunNode)in(3))._tf.fidx()==_fidx) ? null : in(idx);
  }
  
  public    Node ctrl() { return          in(0); } // internal function control
            Node val () { return          in(1); } // standard exit value
  public    Node rpc () { return          in(2); } // Almost surely a PhiNode merging RPCs
  public FunNode fun () { return (FunNode)in(3); } // Function header
  @Override String xstr() {                        // Self short name
    String name = FunNode.name(_fidx);
    return name==null ? "Epilog" : "Epi#"+name;
  }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns any/top.
  public static Node forward_ref( GVNGCM gvn, Node scope, String name, Parse unkref ) {
    FunNode fun = gvn.init(new FunNode(scope,name));
    String referr = unkref.errMsg("Unknown ref '"+name+"'");
    return new EpilogNode(fun,gvn.con(TypeErr.XSCALAR),gvn.con(TypeRPC.ALL_CALL),fun, referr);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return in(0)== in(3) && fun()._tf.is_forward_ref(); }

  // 'this' is a forward reference, probably with multiple uses (and no inlined
  // callers).  Passed in the matching function definition, which is brand new
  // and has no uses.  Merge the two.
  public void merge_ref_def( GVNGCM gvn, String tok, EpilogNode def ) {
    FunNode rfun = fun();
    FunNode dfun = def.fun();
    assert rfun._defs._len==2 && rfun.in(0)==null && rfun.in(1) instanceof ScopeNode; // Forward ref has no callers
    assert dfun._defs._len==2 && dfun.in(0)==null && dfun.in(1) instanceof ScopeNode;
    assert def._uses._len==0;                      // Def is brand new, no uses

    gvn.subsume(this,def);
    dfun.bind(tok);
  }

  @Override public Type all_type() { return TypeTuple.GENERIC_FUN; }
  
  // Return the op_prec of the returned value.  Not sensible except when call
  // on primitives.
  @Override public byte op_prec() { return val().op_prec(); }
}
