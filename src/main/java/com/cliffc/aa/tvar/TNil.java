package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

public class TNil<T extends TNil<T>> extends TVar {

  @Override public TVar reset_tnode(TNode tn) { return this; }

  // TNil always "unifies" by doing nothing & losing unification.
  @Override boolean _unify0( TVar tv, boolean test ) { return false; }

  @Override final boolean _will_unify(TVar tv, int cnt) { return true; }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) { return sb.p("TNil"); }
  @Override TNode push_dep(TNode tn, VBitSet visit) { return tn; }
}
