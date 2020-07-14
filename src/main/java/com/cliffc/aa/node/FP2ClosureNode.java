package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

// Extract a Display pointer (a TypeMemPtr) from a TypeFunPtr.
public final class FP2ClosureNode extends Node {
  public FP2ClosureNode( Node funptr ) {
    super(OP_FP2CLO,funptr);
  }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // If copy is dead, optimize for it.
    Node c = in(0).is_copy(gvn,CallNode.ARGIDX);
    if( c != null )
      set_def(0,c,gvn);
    // If at a FunPtrNode, it is only making a TFP out of a code pointer and a
    // display.  Become the display (dropping the code pointer).
    if( in(0) instanceof FunPtrNode )
      return in(0).in(1);

    return c==null ? null : this;
  }
  @Override public Type value(GVNGCM gvn) {
    // Expect either a TFP from a FunPtrNode, or a TypeTuple from a CallNode.
    Type t0 = gvn.type(in(0));
    Type tfp = t0 instanceof TypeTuple ? CallNode.ttfp(t0) : t0;
    return convert(tfp).simple_ptr();
  }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return TypeMem.ANYMEM; }
  static public Type convert( Type t ) {
    if( !(t instanceof TypeFunPtr) )
      return t.above_center() ? TypeFunPtr.DISP.dual() : TypeFunPtr.DISP;
    TypeFunPtr tfp = (TypeFunPtr)t;
    return tfp._disp;
  }
}
