package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;
import java.util.function.Predicate;

// A collection of top-level simple types, either a meet-of-joins or a join-of-
// meets, to make the lattice distributed.  A meet of ~Ctrl and ~Scalar will
// fall to... (~Ctrl meet ~Scalar) and not ALL.
public class TypeDist extends Type<TypeDist> {

  // 
  int _bits; // Array of booleans for each simple type being in-or-out.

  private TypeDist ( int bits ) { super(TDIST); init(bits); }
  private void init( int bits ) { super.init(TDIST); _bits = bits; }
  // Hash does not depend on other types
  @Override int compute_hash() { return super.compute_hash()+_bits; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeDist) ) return false;
    TypeDist t2 = (TypeDist)o;
    return super.equals(o) && _bits==t2._bits;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  // True means join-of-low, false meet-of-high
  boolean any   () { return (_bits&(1<<0))==0; }
  boolean ctrl  () { return (_bits&(1<<1))==1; } // CTRL
  boolean scalar() { return (_bits&(1<<2))==1; } // SCALAR

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    sb.p('[');
    if( ctrl  () ) sb.p(oob(Type.CTRL  )).p(',');
    if( scalar() ) sb.p(oob(Type.SCALAR)).p(',');
    return sb.unchar().p(']');
  }
  
  private static TypeDist FREE=null;
  @Override protected TypeDist free( TypeDist ret ) { FREE=this; return ret; }
  private static TypeDist make( int bits ) {
    TypeDist t1 = FREE;
    if( t1 == null ) t1 = new TypeDist(bits);
    else {  FREE = null;       t1.init(bits); }
    TypeDist t2 = (TypeDist)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  TypeDist make( Type t ) {
    assert any() == !t.above_center(); // any() True means join-of-low, so the 't's must be low
    switch( t._type ) {
    case TCTRL  : case TXCTRL  : return make(_bits|1);
    case TSCALAR: case TXSCALAR: return make(_bits|2);
    default: t.typerr(null);
    }
    return null;
  }

  static public  final TypeDist MEET_HI = make(0);
  static public  final TypeDist JOIN_LO = make(1);
  static public  final TypeDist TEST = JOIN_LO.make(Type.CTRL).make(Type.SCALAR);
  static final TypeDist[] TYPES = new TypeDist[]{MEET_HI,TEST};

  @Override protected TypeDist xdual() { return new TypeDist(_bits^1); }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    switch( t._type ) {
    default: throw typerr(t);
    }
  }

  @Override public boolean above_center() { return any(); }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
