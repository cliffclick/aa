package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Tail end of functions.  Gathers:
// - exit control; function may never exit or may be more than one
// - exit memory; updated program state
// - exit value;
// - RPC - where to jump-to next; the Continuation
// - The FunNode function header (quickly maps to SESE region header)
public class EpilogNode extends Node {
  int _fidx;
  private final String _unkref_err; // Unknown ref error (not really a forward ref)
  public EpilogNode( Node ctrl, Node mem, Node val, Node rpc, Node fun, int fidx, String unkref_err ) {
    super(OP_EPI,ctrl,mem,val,rpc,fun);
    _unkref_err = unkref_err;
    _fidx = fidx;              // Record function index, so can tell it exactly
  }
  @Override public Node ideal(GVNGCM gvn) {
    // If is_copy is true, CallNodes uses need to fold away as well
    if( is_copy(gvn,4) != null )
      for( Node use : _uses ) gvn.add_work(use);
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(ctl()); // Function exits, or not
    Type r = gvn.type(rpc()); // Caller; the Continuation
    assert gvn.type(mem()) instanceof TypeMem;
    if( c==Type.ANY  || r==Type.ANY  ) return all_type().dual();
    if( (c!=Type.CTRL && c!=Type.XCTRL) || !(r instanceof TypeRPC) ) return all_type();
    return TypeFunPtr.make(BitsFun.make0(_fidx));
  }
  @Override public String err(GVNGCM gvn) { return is_forward_ref() ? _unkref_err : null; }

  @Override public Node is_copy(GVNGCM gvn, int idx) {
    // FunNode has disappeared/optimized away, so should this Epilog
    return (in(4) instanceof FunNode && fun()._fidx==_fidx) ? null : in(idx);
  }
  
  public    Node ctl() { return          in(0); } // internal function control
  public    Node mem() { return          in(1); } // standard exit memory
  public    Node val() { return          in(2); } // standard exit value
  public    Node rpc() { return          in(3); } // Almost surely a PhiNode merging RPCs
  public FunNode fun() { return (FunNode)in(4); } // Function header
  @Override String xstr() {                       // Self short name
    FunNode fun = FunNode.find_fidx(_fidx);
    return fun==null ? "Epilog" : "Epi#"+fun._name;
  }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns a scalar.
  public static Node forward_ref( GVNGCM gvn, String name, Parse unkref ) {
    FunNode fun = gvn.init(new FunNode(name));
    String referr = unkref.errMsg("Unknown ref '"+name+"'");
    return new EpilogNode(fun,gvn.con(TypeMem.MEM),gvn.con(Type.SCALAR),gvn.con(TypeRPC.ALL_CALL),fun,fun._fidx, referr);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return in(0)== in(4) && in(4) instanceof FunNode && fun().is_forward_ref(); }

  // 'this' is a forward reference, probably with multiple uses (and no inlined
  // callers).  Passed in the matching function definition, which is brand new
  // and has no uses.  Merge the two.
  public void merge_ref_def( GVNGCM gvn, String tok, EpilogNode def ) {
    FunNode rfun = fun();
    FunNode dfun = def.fun();
    assert rfun._defs._len==2 && rfun.in(0)==null && rfun.in(1) == Env.ALL_CTRL; // Forward ref has no callers
    assert dfun._defs._len==2 && dfun.in(0)==null;
    assert def._uses._len==0;                      // Def is brand new, no uses

    gvn.subsume(this,def);
    dfun.bind(tok);
  }

  @Override public TypeFunPtr all_type() { return TypeFunPtr.GENERIC_FUNPTR; }
  
  // True if epilog or function is uncalled (but possibly returned or stored as
  // a constant).  Such code is not searched for errors.
  @Override boolean is_uncalled(GVNGCM gvn) { return !is_forward_ref() && gvn.type(rpc())== TypeRPC.ALL_CALL; }
  
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() {
    return val()._uid < GVNGCM._INIT0_CNT ? val().op_prec() : -1;
  }
}
