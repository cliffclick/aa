package com.cliffc.aa.type;

import com.cliffc.aa.util.*;
import java.util.Arrays;

// Class to make hashcons generic [].  Array.equals is now pointer equality.  Bug
// to change after interning, but the Java type system does not let me easily
// enforce this.
public abstract class AryI<T> {

  abstract Ary<AryI<T>> clinit();
  abstract AryI<T> make_holder(int len);
  abstract T[] make_ary(int len);
  abstract T[][] make_arys(int len);
  abstract int compute_hash(T[] ts);

  // Lazy expanding list of AryI customized to handle various T[] lengths.
  private final Ary<AryI<T>> ARYS = clinit();


  // Make a AryI to handle a T[] of length 'len'
  private AryI<T> tary( int len) {
    AryI<T> tary = ARYS.atX(len);
    return tary==null ? ARYS.setX(len,make_holder(len)) : tary;
  }

  private static final Key K = new Key(null,0);

  // Wrapper to customize array.equals
  private static class Key {
    Object[] _ts;
    int _hash;
    private Key(Object[] ts, int hash) { _ts=ts; _hash = hash; }
    @Override public int hashCode() { return _hash; }
    @Override public boolean equals(Object o) {
      if( !(o instanceof Key key) ) return false;
      Object[] ts = key._ts;
      // This series of tests is NOT the same as Arrays.equals(), since it
      // bottoms out in a pointer-equality test instead of 'equals'.
      if( _ts==ts ) return true;
      if( _ts.length != ts.length ) return false;
      for( int i=0; i<ts.length; i++ )
        if( _ts[i]!=ts[i] )
          return false;
      return true;
    }
  }

  private final int _len;       // Length of arrays being handled
  private final IHashMap _intern = new IHashMap();
  private final Ary<T[]> _free = new Ary<>(make_arys(1),0);
  AryI( int len ) { _len=len; }
  // No internal checks now, appears to be fairly healthy
  private AryI<T> check() { return this; }

  // Return a free T[]
  private T[] get() {
    if( _free.isEmpty() )
      _free.push(make_ary(_len));
    return _free.pop();
  }

  private T[] hash_cons_(T[] ts) {
    K._ts=ts;
    K._hash = compute_hash(ts);
    Key k2 = _intern.get(K);
    if( k2 != null ) {
      if( k2._ts!=ts ) _free.push(ts);
      return (T[])k2._ts;
    }
    _intern.put(new Key(ts,K._hash));
    return ts;
  }
  private boolean interned_(T[] ts) {
    K._ts=ts;
    K._hash = compute_hash(ts);
    Key k2 = _intern.get(K);
    return k2!=null && k2._ts==ts;
  }

  final T[] _get(int len) { return tary(len).check().get(); }
  final void _free(T[] ts) { tary(ts.length)._free.push(ts); }
  final T[] _hash_cons(T[] ts) { return tary(ts.length).check().hash_cons_(ts); }
  final boolean _interned(T[] ts) { return tary(ts.length).interned_ (ts); }
  // Why is this API not auto-interning?  Because it is used to make cyclic
  // types in TStructs, which means the fields will change over
  // time... until the intern point.
  final T[] _ts(T t0) {
    AryI<T> t1 = tary(1).check();
    T[] ts = t1.get();
    ts[0] = t0;
    return ts;
  }
  final T[] _ts(T t0, T t1) {
    AryI<T> t2 = tary(2).check();
    T[] ts = t2.get();
    ts[0] = t0;
    ts[1] = t1;
    return ts;
  }
  final T[] _ts(T t0, T t1, T t2) {
    AryI<T> t3 = tary(3).check();
    T[] ts = t3.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    return ts;
  }
  final T[] _ts(T t0, T t1, T t2, T t3) {
    AryI<T> t4 = tary(4).check();
    T[] ts = t4.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    ts[3] = t3;
    return ts;
  }
  final T[] _ts(T t0, T t1, T t2, T t3, T t4) {
    AryI<T> t5 = tary(5).check();
    T[] ts = t5.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    ts[3] = t3;
    ts[4] = t4;
    return ts;
  }
  final T[] _ts(T t0, T t1, T t2, T t3, T t4, T t5) {
    AryI<T> t6 = tary(6).check();
    T[] ts = t6.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    ts[3] = t3;
    ts[4] = t4;
    ts[5] = t5;
    return ts;
  }

  // Result not interned; suitable for direct hacking.
  // Original assumed in-use, not freed.
  final T[] _clone(T[] ts) {
    T[] ts2 = tary(ts.length).check().get();
    System.arraycopy(ts,0,ts2,0,ts.length);
    return ts2;
  }
  // Result not interned; suitable for direct hacking.
  // Original assumed in-use, not freed.
  final T[] _copyOf(T[] ts, int len) {
    T[] ts2 = tary(len).check().get();
    int minlen = Math.min(len,ts.length);
    System.arraycopy(ts,0,ts2,0,minlen);
    Arrays.fill(ts2,minlen,len,null);
    return ts2;
  }
}
