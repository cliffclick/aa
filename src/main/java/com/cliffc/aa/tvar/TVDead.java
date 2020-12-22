package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.util.*;

import java.util.HashSet;

public class TVDead<T extends TVDead<T>> extends TVar {

  // TVDead always "unifies" by doing nothing & winning unification.
  @Override boolean _unify0( TVar tv, boolean test ) { return false; }

  @Override final boolean _will_unify(TVar tv, int cnt) { return true; }

  // Return a "fresh" copy, preserving structure
  @Override boolean _fresh_unify( int cnt, TVar tv, BitsAlias news, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    throw com.cliffc.aa.AA.unimpl(); 
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) { return sb.p("TVDead"); }
  @Override TNode push_dep(TNode tn, VBitSet visit) { return tn; }
}
