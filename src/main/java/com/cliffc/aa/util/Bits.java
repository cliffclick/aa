package com.cliffc.aa.util;

import com.cliffc.aa.AA;
import org.jetbrains.annotations.NotNull;

import java.util.*;

// Bits supporting a lattice; immutable; hash-cons'd.
public class Bits implements Iterable<Integer> {
  // Holds a set of bits meet'd together, or join'd together, along
  // with an infinite extent or a single bit choice as a constant.
  //
  // If _bits is NULL, then _con holds the single set bit (including 0).
  // If _bits is not-null, then _con is 0 for meet, and -1 for join.
  // The last bit of _bits is the "sign" bit, and extends infinitely.
  private long[] _bits;         // Bits set or null for a single bit
  private int _con;             // value of single bit, or 0 for meet or -1 for join
  private int _hash;            // Pre-computed hashcode
  private      Bits(int con, long[] bits ) { init(con,bits); }
  private void init(int con, long[] bits ) {
    if( bits==null ) assert con >= 0;
    else             assert con==0 || con==-1;

    int sum=con;
    if( bits != null ) for( long bit : bits ) sum += bit;
    _hash=sum;
    _con = con;
    _bits=bits;
  }
  @Override public int hashCode( ) { return _hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof Bits) ) return false;
    Bits bs = (Bits)o;
    if( _con != bs._con || _hash != bs._hash ) return false;
    if( _bits == bs._bits ) return true;
    if( _bits ==null || bs._bits==null ) return false;
    if( _bits.length != bs._bits.length ) return false;
    for( int i=0; i<_bits.length; i++ )
      if( _bits[i]!=bs._bits[i] ) return false;
    return true;
  }
  @Override public String toString() { return toString(new SB()).toString(); }
  public SB toString(SB sb) {
    if( this==FULL ) return sb.p("[ALL]");
    else if( _con==-1 && _bits.length==1 && _bits[0]==-1 ) return sb.p("[~ALL]");
    sb.p('[');
    if( _bits==null ) sb.p(_con);
    else {
      for( Integer idx : this ) sb.p(idx).p(above_center()?'+':',');
    }
    if( inf() ) sb.p("...");
    return sb.p(']');
  }

  private static HashMap<Bits,Bits> INTERN = new HashMap<>();
  private static Bits FREE=null;
  private static Bits make( int con, long[] bits ) {
    Bits t1 = FREE;
    if( t1 == null ) t1 = new Bits(con,bits);
    else { FREE = null; t1.init(con,bits); }
    Bits t2 = INTERN.get(t1);
    if( t2 == null ) INTERN.put(t1,t1);
    else { FREE=t1; t1=t2; }
    return t1;
  }

  private static Bits make0( int con, long[] bits ) {
    assert con==0 || con==-1;
    // TODO: convert to single-bit-form if only 1 bit set
    // TODO: remove trailing sign-extend words
    throw AA.unimpl();
  }        
  public static Bits make( int bit ) {
    if( bit < 0 ) throw new IllegalArgumentException("bit must be positive");
    if( bit >= 63 ) throw AA.unimpl();
    return make(bit,null);
  }
  
  public static Bits FULL = make(0,new long[]{-1});
  
  private static int  idx (int i) { return i>>6; }
  private static long mask(int i) { return 1L<<(i&63); }
  public  boolean inf() { return _bits !=null && (_bits[_bits.length-1]>>63)==-1; }
  
  public int getbit() { assert _bits==null; return _con; }
  public int   abit() { return _bits==null ? _con : -1; }
  public boolean above_center() { return _con==-1; }
  
  public boolean test(int i) {
    if( _bits==null ) return i==_con;
    int idx = idx(i);
    return idx < _bits.length ? (_bits[idx]&mask(i))!=0 : inf();
  }

  private int max() { return (_bits.length<<6)-1; }
  private static void or( long[] bits, int con ) { bits[idx(con)] |= mask(con); }
  private static long[] bits( int a, int b ) { return new long[idx(Math.max(a,b))+1]; }
  
  public Bits meet( Bits bs ) {
    if( this==bs ) return this;
    if( this==FULL || bs==FULL ) return FULL;
    if( _bits==null || bs._bits==null ) { // One or both are constants
      Bits conbs = this, bigbs = bs;
      if( bs._bits==null ) { conbs = bs;  bigbs = this; }
      if( bigbs._bits==null ) { // both constants
        // two constants; make a big enough bits array for both
        long[] bits = bits(conbs._con,bigbs._con);
        or( bits,conbs._con);
        or( bits,bigbs._con);
        Bits bs0 = make(0,bits);
        assert !bs0.inf(); // didn't set sign bit by accident (need bigger array if so)
        return bs0;
      }
      
      if( bigbs._con==0 ) {     // Meet of constant and set
        if( bigbs.test(conbs._con) ) return bigbs; // already a member
        // Grow set to hold constant and OR it it
        long[] bits = bits(bigbs.max(),conbs._con);
        System.arraycopy(bigbs._bits,0,bits,0,bigbs._bits.length);
        or( bits,conbs._con);
        Bits bs0 = make(0,bits);
        assert bs0.inf()==bigbs.inf();
        return bs0;
      }
      // Join of constant and set
      if( bigbs.test(conbs._con) ) return conbs; // Already a member
      throw AA.unimpl();    // join constant and any bit from big set

    }

    if( _con==0 ) {             // Meet
      if( bs._con==0 ) {
        Bits smlbs = this, bigbs = bs;
        if( smlbs._bits.length > bigbs._bits.length ) { smlbs=bs; bigbs=this; }
        long[] bits = bigbs._bits.clone();
        for( int i=0; i<smlbs._bits.length; i++ ) bits[i]|=smlbs._bits[i];
        return make(0,bits);

      } else {                  // Meet of a high set and low set
        // Probably require 1 bit from high set in the low set.
        // For now, just return low set
        return this;
      }
    }
    if( bs._con==0 ) {          // Meet of a low set and high set
      // Probably require 1 bit from high set in the low set.
      // For now, just return low set
      return bs;
    }

    // join of 2 sets; return intersection
    Bits bs0 = this, bs1 = bs;  // Shorter set in bs0
    if( _bits.length > bs._bits.length ) { bs0=bs; bs1=this; }
    boolean eqs=true;
    for( int i=0; i<bs0._bits.length; i++ )
      if( (bs0._bits[i]&bs1._bits[i]) != bs0._bits[i] )
        { eqs=false; break; }
    if( eqs ) return bs0;       // All short bits in long set, return intersection
    throw AA.unimpl();          // 2 big sets
    
  }
  public Bits dual() {
    if( _bits==null ) return this; // Dual of a constant is itself
    // Otherwise just flip _con
    assert _con==0 || _con==-1;
    return make(~_con,_bits);
  }

  /** @return an iterator */
  @NotNull @Override public Iterator<Integer> iterator() { return new Iter(); }
  private class Iter implements Iterator<Integer> {
    int _i=-1;
    @Override public boolean hasNext() {
      if( _bits==null )
        if( _i==-1 ) { _i=0; return true; } else return false;
      int idx;
      while( (idx=idx(++_i)) < _bits.length )
        if( (_bits[idx]&mask(_i)) != 0 )
          return true;
      return false;
    }
    @Override public Integer next() {
      if( _bits==null ) return _con;
      if( idx(_i) < _bits.length ) return _i;
      throw new NoSuchElementException();
    }
  }
}
