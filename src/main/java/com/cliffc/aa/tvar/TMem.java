package com.cliffc.aa.tvar;

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

  // Unify at a single alias
  public void unify_alias(int alias, TVar tv) {
    grow(alias+1);
    TVar tobj = parm(alias);
    if( tobj==null ) _parms[alias] = tv;
    else tobj.unify(tv);
  }
}
