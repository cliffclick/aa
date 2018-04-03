package com.cliffc.aa;

// Type Variables.  Supports type unification via Tarjan U-F
public class TypeVar extends Type {
  TypeVar _unify;
  TypeVar() { super(Type.TANY); }

  // The "find" part of Tarjan U-F
  final TypeVar go() {
    TypeVar top = _unify;
    if( top==null ) return this; // Already itself
    if( top._unify==null ) return top; // Already as short a chain as can get
    // Find the union-chain top
    while( top._unify != null ) top = top._unify;
    TypeVar up = this, next;
    // Set everybody along the chain to the union-chain top
    while( (next=up._unify) != null ) { up._unify = top; up=next; }
    return top;
  }
  
  // The "union" part of Tarjan U-F
  final TypeVar unify( TypeVar t ) { assert _unify==null && t._unify==null; return _unify = t; }
}
