package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;

// Fun TVar, NOT FunPtr!  Gathers incoming function arguments.  Only used AFTER
// a Fun is completed, because Parms/Args are not available when a Fun first is
// created.
public class TArgs extends TMulti<TArgs> {
  public final boolean _unpacked;   // Syntactic de-sugaring on a Call, allows arg-counts to mis-match.

  public TArgs(TNode fun, boolean unpacked ) { this(null,init(fun),unpacked); }
  TArgs(TNode fun, TVar[] parms, boolean unpacked) {
    super(fun,parms);
    _unpacked = unpacked;
  }
  public final int nargs() { return _parms.length; }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TArgs targs) {
    return _parms.length == targs._parms.length ||
      (!_unpacked && !targs._unpacked);
  }

  @Override TArgs _fresh_new() { return new TArgs(null, tvars(_parms.length), _unpacked); }
}
