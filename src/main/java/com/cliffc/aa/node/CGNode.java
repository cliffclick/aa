package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeTuple;

// CallGraph node.  Control flow along a function->call edge.
// Replaces a CProj after Call, and arg checks.
public final class CGNode extends CProjNode {
  public CGNode( CallNode call ) { super(OP_CALLGRF,call,0); }
  @Override String xstr() { return "CG"; }
  @Override public Node ideal(GVNGCM gvn, int level) { return super.ideal(gvn,level); }
  @Override public Type value(GVNGCM gvn) {
    if( _uses._len==0 ) return Type.CTRL;
    TypeTuple tcall = (TypeTuple)gvn.type(in(0));
    assert _uses._len==1;
    FunNode fun = (FunNode)_uses.at(0);
    TypeFunPtr tfp = fun._tf;
    for( int i=0; i<tfp._args._ts.length; i++ ) {
      Type actual = tcall.at(i+2);
      if( i==0 ) actual = FP2ClosureNode.convert(actual); // Strip FP from Closure
      Type formal = tfp.arg(i);
      if( actual==formal ) continue; // Always ok, even for high formals
      if( formal.above_center() ) throw com.cliffc.aa.AA.unimpl();
      // Similar to CallNode.resolve, if any args sideways or too high then
      // XCTRL else CTRL.
      if( !formal.dual().isa(actual) )
        return Type.XCTRL;      // Failed arg check
    }
    return Type.CTRL;
  }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  // CGNodes are never equal, as they are a variant of an edge label.
  @Override public boolean equals(Object o) { return this==o; }
}
