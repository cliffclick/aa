package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.tvar.TV2;
import java.util.Arrays;

// "fresh" the incoming TVar: make a fresh instance.
public class FreshNode extends UnOrFunPtrNode {
  final TV2[] _tv2s;
  public FreshNode( Env.VStack vs, Node ld ) { super(OP_FRESH, ld); _tv2s = vs.compact(); }

  @Override public Node ideal_reduce() {
    if( _tv2s==null || _tv2s.length==0 ) return in(0);
    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) { return val(0); }

  @Override public boolean unify( boolean test ) {  return tvar(0).fresh_unify(tvar(),_tv2s,test); }

  @Override public UnresolvedNode unk() { return in(0) instanceof UnresolvedNode ? (UnresolvedNode)in(0) : null; }
  @Override int nargs() { return ((UnOrFunPtrNode)in(0)).nargs(); }
  @Override public UnOrFunPtrNode filter(int nargs) { return ((UnOrFunPtrNode)in(0)).filter(nargs); }
  @Override public FunPtrNode funptr() {
    return in(0) instanceof UnOrFunPtrNode ? ((UnOrFunPtrNode)in(0)).funptr() : null;
  }

  @Override public int hashCode() { return super.hashCode()+Arrays.hashCode(_tv2s); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    return (o instanceof FreshNode) && Arrays.equals(_tv2s,((FreshNode)o)._tv2s);
  }

}
