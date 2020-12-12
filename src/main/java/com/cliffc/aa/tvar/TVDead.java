package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.*;

import java.util.HashSet;

public class TVDead<T extends TVDead<T>> extends TVar {

  // TVDead always "unifies" by doing nothing & winning unification.
  @Override TVar _unify0( TVar tv ) { return this; }

  @Override final boolean _will_unify(TVar tv, int cnt) { return true; }

  // Return a "fresh" copy, preserving structure
  @Override boolean _fresh_unify( TVar tv, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    throw com.cliffc.aa.AA.unimpl(); 
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) { return sb.p("TVDead"); }
  @Override void push_dep(TNode tn, VBitSet visit) { }
}
