package com.cliffc.aa.util;

import java.util.function.IntSupplier;

// Simple worklist.  Filters dups on a add.
// Constant-time remove until empty.
public class Work<E extends IntSupplier> extends BitSetSparse {
  private final Ary<Object> _work = new Ary<>(new Object[1],0);
  private final int _rseed;
  private int _idx;             // Next item to get
  public Work() { this(123); }
  public Work(int rseed) { _rseed = rseed; }
  public int len() { return _work._len; }
  public boolean isEmpty() { return _work.isEmpty(); }
  public E add(E e) {
    if( e!=null && !tset(e.getAsInt()) )
      _work.push(e);
    return e;
  }
  public void add(E[] es) { if(es!=null) for( E e : es ) add(e); }
  public void addAll(Ary<? extends E> es) { if( es!=null ) for( E e : es ) add(e); }
  public boolean on(E e) { return test(e.getAsInt()); }
  @SuppressWarnings("unchecked")
  public E pop() {
    if( _work._len==0 ) return null;
    _idx = (_idx+_rseed)&((1<<30)-1);
    E e = (E)_work.del( _idx % _work._len );
    clr(e.getAsInt());
    return e;
  }
}
