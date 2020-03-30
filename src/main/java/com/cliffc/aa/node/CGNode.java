package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// CallGraph node.  Control flow along a function->call edge.
// Replaces a CProj after Call, and arg checks.
public final class CGNode extends CProjNode {
  public CGNode( CallNode call ) { super(OP_CALLGRF,call,0); }
  @Override String xstr() { return "CG"; }
  @Override public Node ideal(GVNGCM gvn, int level) { return super.ideal(gvn,level); }
  @Override public Type value(GVNGCM gvn) {
    if( _uses._len==0 ) return Type.CTRL;
    if( _live==TypeMem.DEAD ) return Type.XCTRL; // Dead, kill control
    assert _uses._len==1;
    FunNode fun = (FunNode)_uses.at(0);
    CallNode call = (CallNode)in(0);
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    if( tcall.at(0) != Type.CTRL ) return Type.XCTRL;
    int fidx = fun._tf.fidx();
    int cmp = call.resolve(fidx,tcall._ts);
    return cmp == -1 || cmp == 1 ? Type.CTRL : Type.XCTRL; // Low/good resolve is alive, illegal/high is not
  }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  // CGNodes are never equal, as they are a variant of an edge label.
  @Override public boolean equals(Object o) { return this==o; }
}
