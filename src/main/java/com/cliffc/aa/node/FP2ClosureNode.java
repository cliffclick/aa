package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeMemPtr;

// Extract a Closure pointer (a TypeMemPtr) from a TypeFunPtr.
public final class FP2ClosureNode extends Node {
  public FP2ClosureNode( Node funptr ) {
    super(OP_FP2CLO,funptr);
  }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // If at a FunPtrNode, it is only making a TFP out of a code pointer and a
    // closure.  Become the closure (dropping the code pointer).
    if( in(0) instanceof FunPtrNode )
      return in(0).in(1);
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    return convert(gvn.type(in(0)),gvn);
  }
  @Override public TypeMemPtr all_type() { return TypeMemPtr.CLOSURE_PTR; }
  static public Type convert( Type t, GVNGCM gvn ) {
    if( !(t instanceof TypeFunPtr) )
      return t.above_center() ? TypeMemPtr.CLOSURE_PTR.dual() : TypeMemPtr.CLOSURE_PTR;
    TypeFunPtr tfp = (TypeFunPtr)t;
    return tfp.closure();
  }
}
