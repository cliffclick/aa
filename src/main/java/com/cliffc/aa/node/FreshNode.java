package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.TypeFlt;
import com.cliffc.aa.type.TypeInt;
import com.cliffc.aa.type.TypeMemPtr;

import java.util.Arrays;

// "fresh" the incoming TVar: make a fresh instance.
public class FreshNode extends UnOrFunPtrNode {
  TV2[] _tv2s;
  public FreshNode( Env.VStack vs, Node ld ) { super(OP_FRESH, ld); _tv2s = vs.compact(); }

  @Override public Node ideal_reduce() {
    boolean progress = false;
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
    if( _val.isa(TypeInt.INT64) || _val.isa(TypeFlt.FLT64) || _val.isa(TypeMemPtr.ISUSED0) )
      return in(0);

    // If nothing left, the Fresh never hits the occurs_in check.
    if( _tv2s==null || _tv2s.length==0 ) return in(0);

    return progress ? this : null;
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
