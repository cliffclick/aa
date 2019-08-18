package com.cliffc.aa.node;

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
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    return fun()._tf;
  }
  @Override public Type all_type() { return TypeFunPtr.GENERIC_FUNPTR; }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() { return ret().op_prec(); }
  
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

  
  @Override public String err(GVNGCM gvn) { return is_forward_ref() ? _referr : null; }
}
