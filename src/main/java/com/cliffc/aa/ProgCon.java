package com.cliffc.aa;

// compile-time constant
public class ProgCon extends Prog {
  ProgCon( Type t ) { super(t); assert t.canBeConst(); }
  // Execution of a compile-time constant is to return the constant
  @Override Type go( ) { return _t; }
  @Override public String toString() { return _t.toString(); }
  @Override ProgCon resolve_types(int[]x) {
    if( _t instanceof TypeUnion && ((TypeUnion)_t)._any ) x[0] |= 2; // Has typeunion
    if( _t.equals(Type.ANY) ) x[0] |= 4;                             // Has ANY type
    return this;
  }
  @Override Prog remove_choice(int[]x) { return this; }
}
