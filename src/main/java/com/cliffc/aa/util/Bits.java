package com.cliffc.aa.util;

import com.cliffc.aa.AA;
import java.util.*;

// Bits supporting a lattice; immutable; hash-cons'd.
public class Bits implements Iterable<Integer> {
  private long[] _bits;         // 
  private int _hash;            // Pre-computed hashcode
  private int _bit;             // value of single bit, or 0 for many or -1 for complement
  private Bits(boolean not, long[] bits ) { init(not,bits); }
  private void init(boolean not, long[] bits ) {
    // No trailing zeros allowed; not canonical
    long last = bits.length==0 ? 0 : bits[bits.length-1];
    assert bits.length==0 || last != 0;
    // Scan for a single-bit set
    if( !not ) {
      boolean z=true;
      for( int i=0; i<bits.length-1; i++ )
        z &= bits[i]==0;          // All leading words zero
      _bit = z && ((last&-last)==last) ? 63-Long.numberOfLeadingZeros(last) : 0;
      if( bits.length==0 ) _bit=0;
    } else _bit = -1;           // Flag as complement set
    _bits=bits;
    int sum=_bit;
    for( long bit : bits ) sum += bit;
    _hash=sum;
  }
  @Override public int hashCode( ) { return _hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof Bits) ) return false;
    Bits bs = (Bits)o;
    if( _bit != bs._bit || _hash != bs._hash ) return false;
    if( _bits == bs._bits ) return true;
    if( _bits.length != bs._bits.length ) return false;
    for( int i=0; i<_bits.length; i++ )
      if( _bits[i]!=bs._bits[i] ) return false;
    return true;
  }
  @Override public String toString() { return toString(new SB()).toString(); }
  public SB toString(SB sb) {
    sb.p('[');
    for( Integer idx : this ) sb.p(idx).p(',');
    if( _bit==-1 ) sb.p("...");
    return sb.p(']');
  }

  private static HashMap<Bits,Bits> INTERN = new HashMap<>();
  private static Bits FREE=null;
  public static Bits make( int fidx ) {
    if( fidx >= 64 ) throw AA.unimpl();
    return make(false,new long[]{1L<<fidx});
  }
  public static Bits make( boolean not, long[] bits ) {
    int len = bits.length-1;
    while( len>=0 && bits[len] == (not?-1:0) ) len--;
    if( len+1 < bits.length )   // Trim trailing zeros
      bits = Arrays.copyOf(bits,len+1);
        
    Bits t1 = FREE;
    if( t1 == null ) t1 = new Bits(not,bits);
    else { FREE = null; t1.init(not,bits); }
    Bits t2 = INTERN.get(t1);
    if( t2 == null ) INTERN.put(t1,t1);
    else { FREE=t1; t1=t2; }
    return t1;
  }

  public static Bits FULL = Bits.make(true,new long[0]);
  
  private int  idx (int i) { return i>>6; }
  private long mask(int i) { return 1L<<(i&63); }
  
  public boolean test(int i) {
    int idx = idx(i);
    return idx < _bits.length ? (_bits[idx]&mask(i))!=0 : (_bit<0);
  }

  public int getbit() { assert _bit > 0; return _bit; }
  public int   abit() {                  return _bit; }
  
  public Bits set(int idx) { throw AA.unimpl(); }
  public Bits or( Bits bs ) {
    if( this==bs ) return this;
    long[] maxs = _bits.length < bs._bits.length ? bs._bits : _bits;
    long[] mins = _bits.length < bs._bits.length ? _bits : bs._bits;
    long[] bits = Arrays.copyOf(mins,maxs.length);
    if( (_bits.length < bs._bits.length ? _bit : bs._bit)==-1 )
      for( int i=mins.length; i<bits.length; i++ ) bits[i] = -1;
    for( int i=0; i<bits.length; i++ ) bits[i] |= maxs[i];
    boolean not = _bit == -1 | bs._bit == -1;
    return make(not,bits);
  }
  public Bits flip() {
    long bits[] = Arrays.copyOf(_bits,_bits.length);
    for( int i=0; i<bits.length; i++ ) bits[i] ^= -1;
    return Bits.make(_bit!=-1,bits);
  }
  
  public Bits meet( Bits bs ) {
    if( this==bs ) return this;
    //if( _bit==-1 || bs._bit== -1 )
    //  throw AA.unimpl();
    return or(bs);
  }
  public Bits dual() {
    return flip();
  }

  /** @return an iterator */
  @Override public Iterator<Integer> iterator() { return new Iter(); }
  private class Iter implements Iterator<Integer> {
    int _i=-1;
    @Override public boolean hasNext() {
      int idx;
      while( (idx=idx(++_i)) < _bits.length )
        if( (_bits[idx]&mask(_i)) != 0 )
          return true;
      return false;
    }
    @Override public Integer next() {
      if( idx(_i) < _bits.length ) return _i;
      throw new NoSuchElementException();
    }
  }
}
