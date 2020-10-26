package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.TypeVar;

// Simple interface to limit TypeNode access to Node.
public interface TNode {
  abstract TypeVar tvar();
  abstract boolean is_dead();
  abstract int uid();
}
