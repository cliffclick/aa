package com.cliffc.aa;

import com.cliffc.aa.tvar.TVar;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;

// Simple interface to limit TypeNode access to Node.
public interface TNode {
  abstract String xstr();       // Pretty short string
  abstract int uid();           // Unique ID
  default public int compareTo(TNode tn) { return uid() - tn.uid(); }

  abstract Type val();          // My lattice type
  abstract TVar tvar();         // My Type-Var, with Finding
  abstract TVar _tvar();        // My Type-Var plain for debug print
  abstract TVar tvar(int x);    // My xth input TVar, shortcut

  abstract int len();           // Number of inputs
  abstract TNode[] parms();     // Parameters for a Fun; arguments to a Call

  abstract boolean is_dead();   // Dead already

  abstract boolean is_forward_ref(); // In H-M, Lambda vs LetRec
  static void add_flow(Ary<TNode>deps) { Env.GVN.add_flow(deps); }
  static void add_flow_uses(Ary<TNode>deps) { Env.GVN.add_flow_uses(deps); }
}
