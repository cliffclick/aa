package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// See CallNode comments.  The FunPtrNode converts a RetNode into a constant
// TypeFunPtr with the constant fidx.  Used to allow 1st class functions to be
// passed about.
public final class FunPtrNode extends Node {
  private final String _referr;
  public  FunPtrNode( RetNode ret ) { super(OP_FUNPTR,ret); _referr = null; }
  private FunPtrNode( RetNode ret, String referr ) { super(OP_FUNPTR,ret); _referr = referr; }
  public RetNode ret() { return (RetNode)in(0); }
  public FunNode fun() { return ret().fun(); }
  // Self   short  name
  @Override String xstr() {
    int fidx = ret()._fidx;    // Reliably returns a fidx
    FunNode fun = FunNode.find_fidx(fidx);
    return "*"+(fun==null ? ""+fidx : fun.name());
  }
  // Inline longer name
  @Override String  str() {
    RetNode ret = ret();
    if( ret.is_copy() ) return "*!!!{->}";
    FunNode fun = ret.fun();
    return fun==null ? xstr() : fun.str();
  }

  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    RetNode ret = ret();
    if( ret.is_copy() )
      return FunNode.find_fidx(ret._fidx)._tf;
    return ret.fun()._tf;
  }
  @Override public Type all_type() { return TypeFunPtr.GENERIC_FUNPTR; }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() { return ret().op_prec(); }
  
  // True if function is uncalled (but possibly returned or stored as
  // a constant).  Such code is not searched for errors.
  @Override boolean is_uncalled(GVNGCM gvn) {
    return !is_forward_ref() && ((TypeTuple)gvn.type(ret())).at(0)==Type.XCTRL;
  }
  
  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns a scalar.
  public static FunPtrNode forward_ref( GVNGCM gvn, String name, Parse unkref ) {
    FunNode fun = gvn.init(new FunNode(name));
    RetNode ret = gvn.init(new RetNode(fun,gvn.con(TypeMem.MEM),gvn.con(Type.SCALAR),gvn.con(TypeRPC.ALL_CALL),fun));
    return new FunPtrNode(ret,unkref.forward_ref_err(fun));
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _referr!=null; }

  // 'this' is a forward reference, probably with multiple uses (and no inlined
  // callers).  Passed in the matching function definition, which is brand new
  // and has no uses.  Merge the two.
  public void merge_ref_def( GVNGCM gvn, String tok, FunPtrNode def ) {
    FunNode rfun = fun();
    FunNode dfun = def.fun();
    assert rfun._defs._len==2 && rfun.in(0)==null && rfun.in(1) == Env.ALL_CTRL; // Forward ref has no callers
    assert dfun._defs._len==2 && dfun.in(0)==null;
    assert def ._uses._len==0;  // Def is brand new, no uses
    // Make a function pointer based on the original forward-ref fidx, but with
    // the known types.
    FunNode.FUNS.setX(dfun.fidx(),null); // Track FunNode by fidx
    TypeFunPtr tfp = TypeFunPtr.make(rfun._tf.fidxs(),dfun._tf._args,dfun._tf._ret);
    gvn.setype(def,tfp);
    gvn.unreg(dfun);  dfun._tf = tfp;  gvn.rereg(dfun,Type.CTRL);
    int fidx = def.ret()._fidx = rfun._tf.fidx();
    FunNode.FUNS.setX(fidx,dfun);     // Track FunNode by fidx

    gvn.subsume(this,def);
    dfun.bind(tok);
  }

  
  @Override public String err(GVNGCM gvn) { return is_forward_ref() ? _referr : null; }
}
