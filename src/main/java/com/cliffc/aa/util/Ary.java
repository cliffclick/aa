package com.cliffc.aa.util;

import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.function.Function;
import java.util.function.Predicate;

// ArrayList with saner syntax
public class Ary<E> implements Iterable<E> {
  public E[] _es;
  public int _len;
  public Ary(E[] es) { this(es,es.length); }
  public Ary(E[] es, int len) { _es=es; _len=len; }
  public Ary(Class<E> clazz) { this((E[]) Array.newInstance(clazz, 1),0); }

  /** @return list is empty */
  public boolean isEmpty() { return _len==0; }
  /** @return active list length */
  public int len() { return _len; }
  /** @param i element index
   *  @return element being returned */
  public E at( int i ) {
    range_check(i);
    return _es[i];
  }
  /** @return last element */
  public E last( ) {
    range_check(0);
    return _es[_len-1];
  }
  
  /** Add element in amortized constant time
   *  @param e Element to add at end of list
   *  @return 'this' for flow-coding */
  public Ary<E> add( E e ) {
    if( _len >= _es.length ) _es = Arrays.copyOf(_es,Math.max(1,_es.length<<1));
    _es[_len++] = e;
    return this;
  }

  /** Fast, constant-time, element removal.  Does not preserve order
   *  @param i element to be removed
   *  @return element removed */
  public E del( int i ) {
    range_check(i);
    E tmp = _es[i];
    _es[i]=_es[--_len];
    return tmp;
  }

  /** Slow, linear-time, element removal.  Preserves order.
   *  @param i element to be removed 
   *  @return element removed */
  public E remove( int i ) {
    range_check(i);
    E e = _es[i];
    System.arraycopy(_es,i+1,_es,i,(--_len)-i);
    return e;
  }
  
  /** Remove all elements */
  public void clear( ) { _len=0; }
  
  public E set( int i, E e ) {
    while( i>= _es.length ) _es = Arrays.copyOf(_es,_es.length<<1);
    if( i >= _len ) _len = i+1;
    return (_es[i] = e);
  }
  
  public Ary<E> set_as( E e ) { _es[0] = e; _len=1; return this; }
  
  /** @return compact array version, using the internal base array where possible. */
  public E[] asAry() { return _len==_es.length ? _es : Arrays.copyOf(_es,_len); }

  /** @param f function to apply to each element.  Updates in-place. */
  public Ary<E> map_update( Function<E,E> f ) { for( int i = 0; i<_len; i++ ) _es[i] = f.apply(_es[i]); return this; }
  /** @param P filter out elements failing to pass the predicate; updates in
   *  place and shuffles list. 
   *  @return this, for flow-coding */
  public Ary<E> filter_update( Predicate<E> P ) {
    for( int i=0; i<_len; i++ )
      if( !P.test(_es[i]) )
        del(i--);
    return this;
  }
  /** Sorts in-place 
   *  @param c Comparator to sort by */
  public void sort_update(Comparator<? super E> c ) { Arrays.sort(_es, 0, _len, c);  }
  /** Find the first element matching predicate P, or -1 if none.  Note that
   *  most del calls shuffle the list, so the first element might be random.
   *  @param P Predicate to match
   *  @return index of first matching element, or -1 if none */
  public int find( Predicate<E> P ) {
    for( int i=0; i<_len; i++ )  if( P.test(_es[i]) )  return i;
    return -1;
  }
  /** @return an iterator */
  @Override public Iterator<E> iterator() { return new Iter(); }
  private class Iter implements Iterator<E> {
    int _i=0;
    @Override public boolean hasNext() { return _i<_len; }
    @Override public E next() { return _es[_i++]; }
  }
  
  @Override public String toString() {
    SB sb = new SB().p('{');
    for( int i=0; i<_len; i++ ) {
      if( i>0 ) sb.p(',');
      if( _es[i] != null ) sb.p(_es[i].toString());
    }
    return sb.p('}').toString();
  }

  private void range_check( int i ) {
    if( i>=_len )
      throw new ArrayIndexOutOfBoundsException(""+i+" >= "+_len);
  }

}
