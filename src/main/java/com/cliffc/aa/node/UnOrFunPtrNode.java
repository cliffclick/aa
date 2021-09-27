package com.cliffc.aa.node;

import com.cliffc.aa.Env;

// Simple interface for an Unresolved (of FunPtr) and FunPtr.
public abstract class UnOrFunPtrNode extends Node {
  UnOrFunPtrNode( byte op, Node... funs ) { super(op, funs); }
  abstract int nargs();         // Number of arguments
  public abstract UnOrFunPtrNode filter(int nargs); // Filter; return null or a copy.
  // An Unresolved is a collection of FunPtrs all with the same name.  Balanced
  // ops have the same closing name.  e.g. integer add, float add, string add,
  // and the leading '+' operator.

  // All binop FunPtrs (two arguments) have same operator precedence.  
  public abstract FunPtrNode funptr(); // Sample FunPtr from Unresolved.
  public abstract UnresolvedNode unk();
}
