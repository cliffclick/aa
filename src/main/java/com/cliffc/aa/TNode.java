package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.tvar.TVar;
import org.jetbrains.annotations.NotNull;

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
  static void add_work_all(Ary<TNode>deps) { Env.GVN.add_work_all(deps); }
}
