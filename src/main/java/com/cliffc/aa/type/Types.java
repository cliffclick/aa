package com.cliffc.aa.type;

import com.cliffc.aa.util.*;
import java.util.Arrays;

// Class to make hashcons Type[].
// Bug to change after interning.
public class Types {
  // Lazy expanding list of TypeAry customed to handle various Type[] lengths.
  private static final Ary<Types> TYPEARY = new Ary<>(new Types[1],0);

  // Make a TypeAry to handle Type[] of length 'len'
  private static Types tary( int len) {
    Types tary = TYPEARY.atX(len);
    return tary==null ? TYPEARY.setX(len,new Types(len)) : tary;
  }
  
  private static final Key K = new Key(null,0);

  // Wrapper to customize array.equals
  private static class Key {
    Type[] _ts;
    int _hash;
    private Key(Type[] ts, int hash) { _ts=ts; _hash = hash; }
    private static int hash( Type[] ts ) {
      for( Type t : ts ) Util.add_hash( t._hash);
      return (int)Util.get_hash();
    }
    @Override public int hashCode() { return _hash; }
    @Override public boolean equals(Object o) {
      if( !(o instanceof Key) ) return false;
      Type[] ts = ((Key)o)._ts;
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
  private final Ary<Type[]> _free = new Ary<>(new Type[1][],0);
  private Types( int len ) { _len=len; }

  private Types check() { assert check_();  return this; }
  private boolean check_() {
    //for( Object k : _intern.keySet() )
    //  assert Key.hash(((Key)k)._ts)==((Key)k)._hash; // Basically asserting array not hacked
    return true;
  }
  private boolean check_(Type[] ts) {
    K._ts=ts;
    K._hash = Key.hash(ts);
    Key k2 = _intern.get(K);
    return k2._ts==ts;
  }


  // Return a free Type[]
  private Type[] get() {
    if( _free.isEmpty() )
      _free.push(new Type[_len]);
    return _free.pop();
  }

  private Type[] hash_cons_(Type[] ts) {
    K._ts=ts;
    K._hash = Key.hash(ts);
    Key k2 = _intern.get(K);
    if( k2 != null ) {
      if( k2._ts!=ts ) _free.push(ts);
      return k2._ts;
    }
    _intern.put(new Key(ts,K._hash));
    return ts;
  }

  public static Type[] get(int len) { return tary(len).check().get(); }
  public static void free(Type[] ts) { tary(ts.length)._free.push(ts); }
  public static Type[] hash_cons(Type[] ts) { return tary(ts.length).check().hash_cons_(ts); }
  // Why is this API not auto-interning?  Because it is used to make cyclic
  // types in TypeStructs, which means the fields will change over
  // time... until the intern point.
  public static Type[] ts(Type t0) {
    Types t1 = tary(1).check();
    Type[] ts = t1.get();
    ts[0] = t0;
    return ts;
  }
  public static Type[] ts(Type t0, Type t1) {
    Types t2 = tary(2).check();
    Type[] ts = t2.get();
    ts[0] = t0;
    ts[1] = t1;
    return ts;
  }
  public static Type[] ts(Type t0, Type t1, Type t2) {
    Types t3 = tary(3).check();
    Type[] ts = t3.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    return ts;
  }
  public static Type[] ts(Type t0, Type t1, Type t2, Type t3) {
    Types t4 = tary(4).check();
    Type[] ts = t4.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    ts[3] = t3;
    return ts;
  }
  public static Type[] ts(Type t0, Type t1, Type t2, Type t3, Type t4) {
    Types t5 = tary(5).check();
    Type[] ts = t5.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    ts[3] = t3;
    ts[4] = t4;
    return ts;
  }
  public static Type[] ts(Type t0, Type t1, Type t2, Type t3, Type t4, Type t5) {
    Types t6 = tary(6).check();
    Type[] ts = t6.get();
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
  public static Type[] clone(Type[] ts) {
    Type[] ts2 = tary(ts.length).check().get();
    System.arraycopy(ts,0,ts2,0,ts.length);
    return ts2;
  }
  // Result not interned; suitable for direct hacking.
  // Original assumed in-use, not freed.
  public static Type[] copyOf(Type[] ts, int len) {
    Type[] ts2 = tary(len).check().get();
    int minlen = Math.min(len,ts.length);
    System.arraycopy(ts,0,ts2,0,minlen);
    Arrays.fill(ts2,minlen,len,null);
    return ts2;
  }
  public static boolean eq( Type[] ts0, Type[] ts1 ) {
    if( ts0==ts1 ) return true;
    if( ts0==null || ts1==null ) return false;
    //assert                             tary(ts0.length).check().check_(ts0);
    //assert ts0.length == ts1.length || tary(ts1.length).check().check_(ts1);
    return false;               // No need for deep check, since interned
  }
}
