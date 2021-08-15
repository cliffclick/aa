package com.cliffc.aa.node;

import com.cliffc.aa.Env;

/**
 * Simple interface for an Unresolved (of FunPtr) and FunPtr.
 */
public abstract class UnOrFunPtrNode extends Node {
  UnOrFunPtrNode( byte op, Node... funs ) { super(op, funs); }
  abstract int nargs();         // Number of arguments
  public abstract UnOrFunPtrNode filter(int nargs); // Filter; return null or a copy.
  /**
   * An Unresolved is a collection of FunPtrs, all with the same number of
   * arguments, same operator precedence (same uni/bin-op) and the same name.
   * Balanced ops have the same closing name.
   */
  public abstract FunPtrNode funptr(); // Sample FunPtr from Unresolved.
  public abstract UnresolvedNode unk();
}
