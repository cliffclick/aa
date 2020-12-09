package com.cliffc.aa.tvar;

import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.TNode;

// TVars for aliased memory.  Very similar to a TArgs, except indexed by alias
// number instead of by direct index.  Missing aliases are assumed to be new
// unique TVars and always unify.
public class TMem extends TMulti<TMem> {

  public TMem(TNode mem) { super(mem,new TVar[1]); }
  public TMem(TVar[] parms) { super(null,parms); }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TMem tv) { return true; }

  @Override TMem _fresh_new() { return new TMem(new TVar[_parms.length]); }

  // Unify two TMems, except at the aliases, unify with the given TVar.
  public void unify_alias(TMem tmem, BitsAlias aliases, TVar tv) {
    int alen = aliases.max()+1; // Length of aliases
    grow(Math.max(alen,tmem._parms.length));
    tmem.grow(_parms.length);
    for( int i=0; i<_parms.length; i++ ) {
      TVar lhs =      parm(i);
      TVar rhs = tmem.parm(i);
      if( i<alen && aliases.test_recur(i) ) rhs = tv;
      if( lhs==null && rhs==null ) continue;
      if( lhs==null ) _parms[i] = rhs;
      else lhs.unify(rhs);
    }
  }
}
