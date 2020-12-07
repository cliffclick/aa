package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.*;

// TVars for aliased memory.  Very similar to a TArgs, except indexed by alias
// number instead of by direct index.  Missing aliases are assumed to be new
// unique TVars and always unify.
public class TMem extends TMulti<TMem> {

  public TMem(TNode mem) {
    super(mem,init(mem));
  }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TMem tv) {
    throw com.cliffc.aa.AA.unimpl();
  }

  @Override TMem _fresh_new() {
    throw com.cliffc.aa.AA.unimpl();
  }
  
}
