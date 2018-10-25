package com.cliffc.aa.type;

import java.util.BitSet;
import java.util.function.Consumer;

// Nil types are just a nil, but along a particular type domain.  Used so the
// parser can just parse a '0' as the same nil for all other types.
public class TypeNil extends Type<TypeNil> {
  public  Type _t;
  private TypeNil  ( Type t ) { super(TNIL); init(t); }
  private void init( Type t ) { _t=t; }
  @Override public int hashCode( ) { return TNIL+(_t==null ? 0 : _t.hashCode());  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeNil) ) return false;
    TypeNil t2 = (TypeNil)o;
    return _t==t2._t;
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeNil) ) return false;
    TypeNil t2 = (TypeNil)o;
    return _t==t2._t || (_t!=null && t2._t != null && _t.cycle_equals(t2._t));
  }
  @Override String str( BitSet dups) { return _t==null ? "nil" : _t.str(dups)+(_t.above_center() ? "+0" : "?"); }
  
  private static TypeNil FREE=null;
  @Override protected TypeNil free( TypeNil ret ) { FREE=this; return ret; }
  private static TypeNil make0( Type t ) {
    assert !(t instanceof TypeNil);
    TypeNil t1 = FREE;
    if( t1 == null ) t1 = new TypeNil(t);
    else { FREE = null; t1.init(t); }
    TypeNil t2 = (TypeNil)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static Type make( Type t ) {
    assert !t.isa(NUM); // Numbers fold in zero directly
    return t == SCALAR || t == XSCALAR || t instanceof TypeNil ? t : make0(t);
  }
  
  // This is the Parser's canonical NIL, suitable for initializing all data
  // types.  It is not in the lattice, and is not returned from any meet
  // (except when meet'ing itself).
  public  static final TypeNil NIL  = make0(null);
  public  static final TypeNil OOP  = make0(TypeOop.OOP);
  public  static final TypeNil XOOP = make0(TypeOop.XOOP);
  public  static final TypeNil STR  = make0(TypeStr.STR);
  public  static final TypeNil ABC  = make0(TypeStr.ABC);

  static final TypeNil[] TYPES = new TypeNil[]{OOP,STR,ABC};
  
  @Override public long   getl() { assert is_con(); return 0; }
  @Override public double getd() { assert is_con(); return 0; }

  @Override protected TypeNil xdual() { return _t==null ? this : new TypeNil(_t.dual()); }
  @Override protected Type xmeet( Type t ) {
    if( t == NIL ) return t.xmeet(this); // Swap NIL to left
    if( above_center() ) {         // choice-nil
      if( t instanceof TypeNil ) { // aways keep nil (choice or not)
        return make(_t.meet(((TypeNil)t)._t));
      } else {
        return _t.meet(t);      // toss away nil choice
      }
    } else {                    // must-nil
      if( this == NIL ) {       // Exactly the flexible nil
        if( t.isa(NUM) ) return t.above_center() ? this : t.meet(TypeInt.FALSE); // Fall away from NIL to ZERO
        if( t.base() instanceof TypeNil ) return t.above_center() ? this : t;
        if( !t.above_center() ) return make(t); // NIL-wrap the other guy
        return make(t.dual());
      }
      if( t instanceof TypeNil )
        return make(_t.meet(((TypeNil)t)._t));
      Type mt = _t.meet(t);
      assert !mt.above_center(); // this is below_center, so the meet is also
      assert !mt.isa(NUM);
      return make(mt);
    }
  }

  @Override public boolean above_center() { return _t != null && _t.above_center(); }
  @Override public boolean may_be_con() { return _t==null || _t.may_be_con(); }
  @Override public boolean is_con()   { return _t == null; } // Constant nil
  @Override public byte isBitShape(Type t) { return _t==null || this==t ? 0 : _t.isBitShape(t); }
  // Make a (posssibly cyclic & infinite) named type.  Prevent the infinite
  // unrolling of names by not allowing a named-type with depth >= D from
  // holding (recursively) the head of a named-type cycle.  We need to cap the
  // unroll, to prevent loops/recursion from infinitely unrolling.
  @Override Type make_recur(TypeName tn, int d, BitSet bs ) {
    if( _t==null ) return this; // No recursion on NIL
    Type t2 = _t.make_recur(tn,d,bs);
    // Build a depth-limited version of the same TypeNil
    return t2==_t ? this : make(t2);
  }
  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { c.accept(_t); }
}
