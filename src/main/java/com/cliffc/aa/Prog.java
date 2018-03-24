package com.cliffc.aa;

/** an implementation of language AA
 */

public abstract class Prog {
  Type _t;
  Prog( Type t ) { _t=t; }
  abstract public String toString();
  abstract Type go( );
  
  // First check that the program is well-typed: constant-fold all evaluations
  // not involving loops (or recursion?), and one what remains alive check that
  // nothing is badly formed: function application is matched with functions
  // (or function unions) and argument counts align.  Report any errors here
  // and stop.
  //
  // If no errors, but yet ambiguity remains, attempt to toss out function
  // choices where some choice requires non-trivial conversions and repeat the
  // above contant folding.  The program should remain well-formed (because
  // removing a choice in one place cannot remove all choices somewhere else).
  //
  // If ambiguity yet remains, then the program should complain about
  // unresolved choices.

  final Prog resolve() {
    Prog p = this;
    int[] x = new int[1];       // horrible 2-value returns (Prog p and x[0])
    // Union of bits:
    // 1 ==> no-progress | progress
    // 2 ==> no-union    | unions - type-unions, places we can remove some choice
    // 4 ==> no-typerr   | typerr (ANY for some reachable type)
    x[0] = 1|2;                 // Set progress & unions
    // TODO: Lousy algo running time, needs Sea-of-Nodes incremental update
    while( (x[0]&1) != 0 ) {    // While progress
      boolean has_union = (x[0]&2)!=0;
      x[0] = 0;                 // Reset
      if( has_union )           // Remove some single union choice
        p = p.remove_choice(x);
      p = p.resolve_types(x);   // Resolve; refresh x
    }
    if( (x[0]&4) != 0 )
      throw new RuntimeException("program has type errors");
    return p;
  }
  abstract Prog resolve_types(int[]x);
  abstract Prog remove_choice(int[]x);
}
