package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;

// "fresh" the incoming TVar: make a fresh instance.
public class FreshNode extends UnOrFunPtrNode {
  final Env.VStack _vs;
  public FreshNode( Env.VStack vs, Node ld ) { super(OP_FRESH, ld); _vs=vs; }

  @Override public Node ideal_reduce() {
    if( _vs==null || _vs.isEmpty() ) return in(0);
    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) { return val(0); }

  @Override public boolean unify( boolean test ) {  return tvar(0).fresh_unify(tvar(),_vs,test); }

  @Override int nargs() { return ((UnOrFunPtrNode)in(0)).nargs(); }
  @Override public UnOrFunPtrNode filter(int nargs) { return ((UnOrFunPtrNode)in(0)).filter(nargs); }
  @Override public FunPtrNode funptr() { return ((UnOrFunPtrNode)in(0)).funptr(); }

  @Override public int hashCode() { return super.hashCode()+_vs.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    return (o instanceof FreshNode) && _vs==((FreshNode)o)._vs;
  }

}
