package com.cliffc.aa;

import java.util.Arrays;
import java.util.HashMap;

/** an implementation of language AA
 */

// Type Variables.  Supports type unification via Tarjan U-F
public class TypeVar {
  final Type _t;
  TypeVar _unify;
  TypeVar( Type t ) { _t=t; }

  // The "find" part of Tarjan U-F
  final Type go() {
    Type top = _unify;
    if( top==null ) return this; // Already itself
    if( top._unify==null ) return top; // Already as short a chain as can get
    // Find the union-chain top
    while( top._unify != null ) top = top._unify;
    Type up = this, next;
    // Set everybody along the chain to the union-chain top
    while( (next=up._unify) != null ) { up._unify = top; up=next; }
    return top;
  }
  
  // The "union" part of Tarjan U-F
  final Type unify( Type t ) { assert _unify==null && t._unify==null; return _unify = t; }
}
