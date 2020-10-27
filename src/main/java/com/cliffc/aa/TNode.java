package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.tvar.TVar;

// Simple interface to limit TypeNode access to Node.
public interface TNode {
  abstract TVar tvar();         // My TVar
  abstract TVar tvar(int x);    // My xth input TVar
  abstract TVar targ(int x);    // Only for functions, my xth argument (parm, not input)
  abstract TVar tret();         // Only for functions, my return TVar (triple of [Control,Memory,Value])
  abstract boolean is_dead();
  abstract int uid();
}
