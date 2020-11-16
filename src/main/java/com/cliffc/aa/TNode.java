package com.cliffc.aa;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.tvar.TVar;
import org.jetbrains.annotations.NotNull;

// Simple interface to limit TypeNode access to Node.
public interface TNode extends Comparable<TNode> {
  abstract Type val();          // My lattice type
  abstract TVar tvar();         // My Type-Var, with Finding
  abstract TVar _tvar();        // My Type-Var plain for debug print
  abstract TVar tvar(int x);    // My xth input TVar
  abstract int len();           // Number of inputs
  abstract boolean is_dead();   // Dead already
  abstract int uid();           // Unique ID
  abstract String xstr();       // Pretty short string
  abstract TNode[] parms();     // Parameters for a Fun; arguments to a Call
}
