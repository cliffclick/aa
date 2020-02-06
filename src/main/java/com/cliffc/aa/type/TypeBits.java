package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;
import java.util.Arrays;

// Simple bit-set.  Hash-consed and immutable.
// Last bit "sign extends" forever.
public class TypeBits extends Type<TypeBits> {
  private long[] _bits;         //
  private TypeBits (long[] bits) { super(TBITS); init(bits); }
  private void init(long[] bits) {
    super.init(TBITS);
    _bits = bits;
  }
  @Override int compute_hash() { return super.compute_hash() + Arrays.hashCode(_bits);  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeBits) || !super.equals(o) ) return false;
    TypeBits tb = (TypeBits)o;
    if( _bits.length != tb._bits.length ) return false;
    return Arrays.equals(_bits,tb._bits);
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups) {
    if( this==FULL  ) return "~[]";
    if( this==EMPTY ) return "[]";
    SB sb = new SB();
    if( !above_center() ) // Print the inverse bits for inverted sets
      return sb.p('~').p(dual().str(dups)).toString();
    sb.p('[');
    // Max bit equal to the sign bit with the prior bit different.
    int max = max();
    for( int i=0; i<max; i++ )
      if( test(i) )
        sb.p(i).p(',');
    return sb.unchar().p(']').toString();
  }
  private static TypeBits FREE=null;
  @Override protected TypeBits free( TypeBits ret ) { FREE=this; return ret; }
  public static TypeBits make( long[] ls ) {
    assert ls.length > 0 && (ls.length==1 || (ls[ls.length-1] !=0 && ls[ls.length-1] != -1));
    TypeBits t1 = FREE;
    if( t1 == null ) t1 = new TypeBits(ls);
    else {   FREE = null;      t1.init(ls); }
    TypeBits t2 = (TypeBits)t1.hashcons();
    if( t1!=t2 ) return t1.free(t2);
    return t1;
  }
  public static final TypeBits make(int... bits) {
    int max=0;
    for( int bit : bits ) max=Math.max(max,bit);
    long[] ls = new long[idx(max)+1];
    for( int bit : bits ) 
      ls[idx(bit)] |= mask(bit);
    return make(ls);
  }
  
  public  static final TypeBits EMPTY = make(new long[1]);
  public  static final TypeBits FULL  = EMPTY.dual();
  static final TypeBits[] TYPES = new TypeBits[]{EMPTY};

  @Override protected TypeBits xdual() {
    long[] bits = new long[_bits.length];
    for( int i=0; i<_bits.length; i++ )
      bits[i] = ~_bits[i];
    return new TypeBits(bits);
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TSTR:
    case TSTRUCT:
    case TOBJ:
    case TNIL:
    case TTUPLE:
    case TFUNPTR:
    case TMEMPTR:
    case TFLT:
    case TINT:
    case TFUN:
    case TRPC:
    case TMEM:   return ALL;
    case TBITS:   break;
    default: throw typerr(t);
    }
    if( this== FULL || t == FULL ) return FULL;
    if( this==EMPTY ) return t   ;
    if( t   ==EMPTY ) return this;
    TypeBits ts = (TypeBits)t;
    long[] bits = new long[_bits.length];
    for( int i=0; i<_bits.length; i++ )
      bits[i] = _bits[i] | ts._bits[i];
    return make(bits);
  }

  private static int  idx (long i) { return (int)(i>>6); }
  private static long mask(long i) { return 1L<<(i&63); }
  private boolean sign() { return (_bits[_bits.length-1]&(1L<<63)) != 0; }
  boolean test(int i) { return idx(i) < _bits.length ? (_bits[idx(i)]&mask(i))!=0 : sign(); }
  // Last bit# equal to the sign, with the prior bit different.
  int max() {
    if( this==FULL || this==EMPTY ) return 1;
    long last = _bits[_bits.length-1];
    if( last < 0 ) last = ~last; 
    return (64 - Long.numberOfLeadingZeros(last))+((_bits.length-1)<<6);
  }

  public TypeBits set(int bit) {
    if( test(bit) ) return this;
    long[] bits = Arrays.copyOf(_bits,idx(bit+1/*do not flip sign bit*/)+1);
    bits[idx(bit)] |= mask(bit);
    return make(bits);
  }
  public TypeBits clr(int bit) {
    if( !test(bit) ) return this;
    if( idx(bit+1/*do not flip sign bit*/) < _bits.length ) {
      long[] bits = _bits.clone();
      bits[idx(bit)] &= mask(bit);
      return make(bits);
    }
    throw com.cliffc.aa.AA.unimpl();
  }
  
  @Override public boolean above_center() { return !sign(); }

  @Override public boolean may_be_con() { throw com.cliffc.aa.AA.unimpl(); }
  @Override public boolean is_con() { throw com.cliffc.aa.AA.unimpl(); }
  @Override public Type meet_nil() { throw com.cliffc.aa.AA.unimpl(); }
  @Override public byte isBitShape(Type t) { throw com.cliffc.aa.AA.unimpl(); }
  @Override public Type widen() { throw com.cliffc.aa.AA.unimpl(); }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
  // Flip low to high
  @Override public TypeBits startype() { return above_center() ? this : dual(); }
}
