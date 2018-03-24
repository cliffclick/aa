package com.cliffc.aa;

// Variable lookup
public class ProgVar extends Prog {
  private final String _name;
  ProgVar( String name, Type t ) { super(t); _name = name; }
  @Override Type go( ) { throw AA.unimpl(); }
  @Override public String toString() { return _name; }
  @Override Prog resolve_types(int[]x) {
    throw AA.unimpl();
    //if( _t instanceof TypeUnion && ((TypeUnion)_t)._any ) x[0] |= 2; // Has typeunion
    //if( _t.equals(Type.ANY) ) x[0] |= 4;                             // Has ANY type
    //return _t.isCon() ? new ProgCon(_t) :  this;
  }
  @Override Prog remove_choice(int[]x) { return this; }
}
