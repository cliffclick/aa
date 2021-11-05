package com.cliffc.aa.util;

import java.util.function.IntSupplier;

// Simple worklist.  Filters dups on a add.
// Constant-time remove until empty.
public class Work<E extends IntSupplier> extends NonBlockingHashMapLong<E> {
  public E add(E e) { if( e!=null ) put(e.getAsInt(),e); return e; }
  public boolean on(E e) { return containsKey(e.getAsInt()); }
  public E pop() {
    long k = getKey();        // Get any random key
    return k==0 ? null : remove(k);
  }
}
