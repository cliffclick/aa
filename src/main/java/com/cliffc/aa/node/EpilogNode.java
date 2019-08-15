package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Tail end of functions.  Gathers:
// - The FunNode function header (quickly maps to SESE region header)
// - The RetNode which gathers: control (function exits or not), memory, value, rpc
public class EpilogNode extends Node {
  int _funuid;     // Used when the function dies, keep the correct SESE region
  TypeFunPtr _tfp; // Used when the function dies, to keep a sane type
  private final String _unkref_err; // Unknown ref error (not really a forward ref)
  public EpilogNode( FunNode fun, Node ret, String unkref_err ) {
    super(OP_EPI,fun,ret);
    _funuid = fun._uid;
    _tfp = fun._tf;
    _unkref_err = unkref_err;
  }
  // FunNode has disappeared/optimized away, so should this Epilog
  @Override public Node is_copy(GVNGCM gvn, int idx) { return is_copy() ? (idx==0 ? ret().in(0) : in(idx)) : null; }
  private boolean is_copy() { return in(0)._uid != _funuid; }
  @Override public Node ideal(GVNGCM gvn) {
    // If is_copy is true, CallNodes uses need to fold away as well
    if( is_copy() )
      for( Node use : _uses ) gvn.add_work(use);
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    if( is_forward_ref() ) return _tfp.startype();
    return _tfp;
  }
  @Override public String err(GVNGCM gvn) { return is_forward_ref() ? _unkref_err : null; }

  public FunNode fun() { return (FunNode)in(0) ; } // Function
  public RetNode ret() { return (RetNode)in(1) ; } // Return
  @Override String xstr() { return "Epi#"+_tfp;  }
  int fidx() { return _tfp.fidx(); }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns a scalar.
  public static Node forward_ref( GVNGCM gvn, String name, Parse unkref ) {
    String referr = unkref.errMsg("Unknown ref '"+name+"'");
    FunNode fun = gvn.init(new FunNode(name));
    RetNode ret = gvn.init(new RetNode(fun,gvn.con(TypeMem.MEM),gvn.con(Type.SCALAR),gvn.con(TypeRPC.ALL_CALL)));
    return new EpilogNode(fun,ret, referr);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _tfp.is_forward_ref(); }

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

  @Override public TypeFunPtr all_type() { return _tfp; }
  
  // True if epilog or function is uncalled (but possibly returned or stored as
  // a constant).  Such code is not searched for errors.
  @Override boolean is_uncalled(GVNGCM gvn) { return !is_forward_ref() && gvn.type(ret().rpc())== TypeRPC.ALL_CALL; }
  
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() {
    return ret().val()._uid < GVNGCM._INIT0_CNT ? ret().val().op_prec() : -1;
  }
}
