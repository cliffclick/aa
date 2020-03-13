package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// See CallNode and FunNode comments. The FunPtrNode converts a RetNode into a
// TypeFunPtr with a constant fidx and variable displays.  Used to allow 1st
// class functions to be passed about.
public final class FunPtrNode extends ConNode<TypeFunPtr> {
  private final String _referr;
  public  FunPtrNode( RetNode ret, Node display, TypeFunPtr tfp ) {
    super(OP_FUNPTR,tfp,ret,display);
    _referr = null;
  }
  // For forward-refs only; super weak display & function.
  private FunPtrNode( String referr, RetNode ret, Node display ) {
    super(OP_FUNPTR,TypeFunPtr.GENERIC_FUNPTR,ret,display);
    _referr = referr;
  }
  @Override public int hashCode() { return super.hashCode() ^ ((_defs._len==0 || in(0)==null) ? 0 : in(0)._uid); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof FunPtrNode) ) return false;
    FunPtrNode fptr = (FunPtrNode)o;
    if( _defs._len!=2 ) return false;
    return _t==fptr._t && in(0)==fptr.in(0) && in(1)==fptr.in(1) && super.equals(fptr);
  }
  public RetNode ret() { return (RetNode)in(0); }
  public Node display(){ return in(1); }
  public FunNode fun() { return ret().fun(); }
  // Self short name
  @Override String xstr() {
    if( is_dead() ) return "*fun";
    int fidx = ret()._fidx;    // Reliably returns a fidx
    FunNode fun = FunNode.find_fidx(fidx);
    return "*"+(fun==null ? ""+fidx : fun.name());
  }
  // Inline longer name
  @Override String str() {
    if( is_dead() ) return "DEAD";
    RetNode ret = ret();
    if( ret.is_copy() ) return "gensym:"+xstr();
    FunNode fun = ret.fun();
    return fun==null ? xstr() : fun.str();
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    if( is_forward_ref() ) return null;
    RetNode ret = ret();
    FunNode fun = ret.is_copy() ? FunNode.find_fidx(ret._fidx) : ret.fun();
    if( display()!=null && (ret.is_copy() || fun._tf.arg(0)==TypeStruct.NO_DISP) )
      { set_def(1,null,gvn); return this; }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    // Always the display is better than the default, since it comes from some
    // real function.
    assert display()==null || is_forward_ref() || ((TypeFunPtr)gvn.self_type(this)).display() != TypeMemPtr.DISPLAY_PTR;
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    RetNode ret = ret();
    FunNode fun = ret.is_copy() ? FunNode.find_fidx(ret._fidx) : ret.fun();
    if( is_forward_ref() ) return fun._tf;
    Type tret = gvn.type(ret);
    Type tdisp = display()==null ? TypeStruct.NO_DISP : gvn.type(display());
    assert tdisp != TypeMemPtr.DISPLAY_PTR;
    return fun._tf.make(tdisp,((TypeTuple)tret).at(2));
  }

  @Override public TypeMem live( GVNGCM gvn) {
    // Pre-GCP, if the function is anywhere alive it might be used in a call
    // and thus demands all the memory that the CallEpi demands.
    // Post-GCP, all things are resolved and normal liveness flows.
    return gvn._opt_mode < 2 ? TypeMem.FULL : super.live(gvn);
  }
  // A function pointer can be applied at a Call, in which case the associated
  // Ret demands everything the CallEpi demands.  Until GCP we assume this
  // FunPtr might end up at any Call.
  @Override public boolean basic_liveness() { return false; }

  @Override public String toString() { return super.toString(); }
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
    return new FunPtrNode(unkref.forward_ref_err(fun),ret,gvn.con(TypeMemPtr.DISPLAY_PTR));
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
