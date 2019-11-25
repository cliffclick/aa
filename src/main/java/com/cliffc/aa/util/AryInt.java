package com.cliffc.aa.util;

import org.jetbrains.annotations.NotNull;

import java.lang.reflect.Array;
import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
  
// ArrayList with saner syntax
public class AryInt {
  public int[] _es;
  public int _len;
  public AryInt(int[] es) { this(es,es.length); }
  public AryInt(int[] es, int len) { _es=es; _len=len; }
  public AryInt() { this(new int[1],0); }

  /** @return list is empty */
  public boolean isEmpty() { return _len==0; }
  /** @return active list length */
  public int len() { return _len; }
  /** @param i element index
   *  @return element being returned; throws if OOB */
  public int at( int i ) {
    range_check(i);
    return _es[i];
  }
  /** @param i element index
   *  @return element being returned, or null if OOB */
  public int atX( int i ) {
    return i < _len ? _es[i] : null;
  }
  /** @return last element */
  public int last( ) {
    range_check(0);
    return _es[_len-1];
  }
  
  /** @return remove and return last element */
  public int pop( ) {
    range_check(0);
    return _es[--_len];
  }
  
  /** Add element in amortized constant time
   *  @param e intlement to add at end of list
   *  @return 'this' for flow-coding */
  public AryInt add( int e ) {
    if( _len >= _es.length ) _es = Arrays.copyOf(_es,Math.max(1,_es.length<<1));
    _es[_len++] = e;
    return this;
  }

  /** Add element in amortized constant time
   *  @param e intlement to add at end of list
   **/
  public void push( int e ) {
    if( _len >= _es.length ) _es = Arrays.copyOf(_es,Math.max(1,_es.length<<1));
    _es[_len++] = e;
  }

  /** Slow, linear-time, element insert.  Preserves order.
   *  @param i index to insert at, between 0 and _len inclusive.
   *  @param e intlement to insert
   */
  public void insert( int i, int e ) {
    if( i < 0 || i>_len )
      throw new ArrayIndexOutOfBoundsException(""+i+" >= "+_len);
    if( _len >= _es.length ) _es = Arrays.copyOf(_es,Math.max(1,_es.length<<1));
    System.arraycopy(_es,i,_es,i+1,(_len++)-i);
    _es[i] = e;
  }
  
  /** Fast, constant-time, element removal.  Does not preserve order
   *  @param i element to be removed
   *  @return element removed */
  public int del( int i ) {
    range_check(i);
    int tmp = _es[i];
    _es[i]=_es[--_len];
    return tmp;
  }

  /** Slow, linear-time, element removal.  Preserves order.
   *  @param i element to be removed 
   *  @return element removed */
  public int remove( int i ) {
    range_check(i);
    int e = _es[i];
    System.arraycopy(_es,i+1,_es,i,(--_len)-i);
    return e;
  }
  
  /** Remove all elements */
  public void clear( ) { _len=0; }

  // Extend and set
  public int setX( int i, int e ) {
    while( i>= _es.length ) _es = Arrays.copyOf(_es,_es.length<<1);
    if( i >= _len ) _len = i+1;
    return (_es[i] = e);
  }
  
  public int set( int i, int e ) {
    range_check(i);
    return (_es[i] = e);
  }
  
  public AryInt set_as( int e ) { _es[0] = e; _len=1; return this; }
  public AryInt set_len( int len ) {
    if( len > _len )
      while( len>= _es.length ) _es = Arrays.copyOf(_es,_es.length<<1);
    _len = len;
    while( _es.length > (len<<1) ) // Shrink if hugely too large
      _es = Arrays.copyOf(_es,_es.length>>1);
    return this;
  }
  
  /** @param c Collection to be added */
  public AryInt addAll( Collection<? extends Integer> c ) { for( int e : c ) add(e); return this; }
    
  /** @param es Array to be added */
  public AryInt addAll( int[] es ) {
    if( es.length==0 ) return this;
    while( _len+es.length > _es.length ) _es = Arrays.copyOf(_es,_es.length<<1);
    System.arraycopy(es,0,_es,_len,es.length);
    _len += es.length;
    return this;
  }
    
  /** @return compact array version, using the internal base array where possible. */
  public int[] asAry() { return _len==_es.length ? _es : Arrays.copyOf(_es,_len); }

  /** Sorts in-place */
  public void sort_update() { Arrays.sort(_es, 0, _len);  }
  /** Find the first matching element using ==, or -1 if none.  Note that
   *  most del calls shuffle the list, so the first element might be random.
   *  @param e intlement to find
   *  @return index of first matching element, or -1 if none */
  public int find( int e ) {
    for( int i=0; i<_len; i++ )  if( _es[i]==e )  return i;
    return -1;
  }

  @Override public String toString() {
    SB sb = new SB().p('[');
    for( int i=0; i<_len; i++ )
      sb.p(_es[i]).p(',');
    return sb.unchar().p(']').toString();
  }

  private void range_check( int i ) {
    if( i < 0 || i>=_len )
      throw new ArrayIndexOutOfBoundsException(""+i+" >= "+_len);
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof AryInt) ) return false;
    AryInt ary = (AryInt)o;
    if( _len != ary._len ) return false;
    if( _es == ary._es ) return true;
    for( int i=0; i<_len; i++ )
      if( _es[i] != ary._es[i] )
        return false;
    return true;
  }
  @Override public int hashCode( ) {
    int sum=_len;
    for( int i=0; i<_len; i++ )
      sum += _es[i];
    return sum;
  }
}
