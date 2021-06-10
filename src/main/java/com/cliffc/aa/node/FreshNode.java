package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import java.util.Arrays;

// "fresh" the incoming TVar: make a fresh instance.
public class FreshNode extends UnOrFunPtrNode {
  TV2[] _tv2s;
  public FreshNode( Env.VStack vs, Node ld ) { super(OP_FRESH, ld); _tv2s = vs.compact(); }

  @Override public Node ideal_reduce() {
    if( in(0)==this ) return null; // Dead self-cycle
    // TODO: Turn on, and also remove dups.
    // Possibly go to Ary<>, for easier removal.
    // Possibly keep sorted, for easier dup removal.
    // Removing or U-F rollup changes hash.
    //// Remove any dead TVars, as they never modify the occurs_in check.
    //int j=_tv2s.length;
    //for( int i=0; i<_tv2s.length; i++ )
    //  if( TV2.get(_tv2s,i).is_dead() )
    //    _tv2s[i] = _tv2s[--j];
    //progress = j != _tv2s.length;
    //if( progress ) _tv2s = Arrays.copyOf(_tv2s,j);

    // Remove Fresh of base type values: things that can never have structure.
    if( no_tvar_structure(_val) )
      return in(0);

    // If nothing left, the Fresh never hits the occurs_in check, and always
    // requires a fresh unify.
    //if( _tv2s==null || _tv2s.length==0 ) return in(0);

    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) { return val(0); }
  @Override public void add_flow_extra(Type old) {
    // Types changed, now might collapse
    if( !no_tvar_structure(old) && no_tvar_structure(_val) )
      Env.GVN.add_reduce(this);
  }
  // Things that can never have type-variable internal structure.
  private static boolean no_tvar_structure(Type t) {
    return t.isa(TypeInt.INT64) || t.isa(TypeFlt.FLT64) || t.isa(TypeMemPtr.ISUSED0);
  }

  @Override public boolean unify( boolean test ) {  return tvar(0).fresh_unify(tvar(),_tv2s,test); }
  
  @Override public byte op_prec() { return in(0).op_prec(); }

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
