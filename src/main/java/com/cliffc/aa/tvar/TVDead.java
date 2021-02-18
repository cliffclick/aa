package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.NonBlockingHashMap;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashSet;

public class TVDead<T extends TVDead<T>> extends TVar {

  @Override final boolean _will_unify(TVar tv, int cnt) { return true; }

  // Return a "fresh" copy, preserving structure
  @Override boolean _fresh_unify( int cnt, TVar tv, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    return false;
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) { return sb.p("TVDead"); }
  @Override public TNode push_dep(TNode tn, VBitSet visit) { return tn; }
}
