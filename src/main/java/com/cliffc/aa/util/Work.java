package com.cliffc.aa.util;

import java.util.function.IntSupplier;

// Simple worklist.  Filters dups on a add.
// Constant-time remove until empty.
// Supports psuedo random pop.
@SuppressWarnings("unchecked")
public class Work<E extends IntSupplier> extends BitSetSparse {
  private final Ary<E> _work = new Ary(new Object[1],0);
  private int _rseed;           // Psuedo-random draw
  private int _idx;             // Next item to get
  public Work() { this(123); }  // Default seed
  public Work(int rseed) { _rseed = rseed; }
  public int len() { return _work._len; }
  public boolean isEmpty() { return _work.isEmpty(); }
  public E add(E e) {           // Add, filtering dups
    if( e!=null && !tset(e.getAsInt()) )
      _work.push(e);
    return e;
  }
  public void setSeed(int rseed ) {
    assert _work.isEmpty();
    _rseed = rseed;
    _idx = 0;
  }
  @Override public Work clear() {
    super.clear();
    _work.clear();
    return this;
  }
  // Bulk adders
  public void add(E[] es) { if(es!=null) for( E e : es ) add(e); }
  public void addAll(Ary<? extends E> es) { if( es!=null ) for( E e : es ) add(e); }
  public void addAll(Work<E> work) { for( Object o : work._work ) add((E)o); }
  public boolean on(E e) { return test(e.getAsInt()); }
  // Pull a psuedo-random element.  Order depends on rseed.
  public E pop() {
    if( _work._len==0 ) return null;
    _idx = (_idx+_rseed)&((1<<30)-1);
    E e = _work.del( _idx % _work._len );
    clr(e.getAsInt());
    return e;
  }
  public E pop_last() {
    if( _work._len==0 ) return null;
    E e = _work.pop();
    clr(e.getAsInt());
    return e;
  }
  // Get/delete "idx"th elements; error if OOB.
  public E at(int idx) { return _work.at(idx); }
  public void del(int idx) { clr((_work.del(idx)).getAsInt()); }
  public String print_work() { return _work.toString(); }
  @Override public String toString() {
    if( _set.size()==0 ) return "[]";
    SB sb = new SB().p('[');
    for( E e : _work )
      sb.p(e.getAsInt()).p(',');
    return sb.unchar().p(']').toString();
  }
}
