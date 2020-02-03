package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.IHashMap;

// Class to make hashcons Type[].
// Bug to change after interning.
public class TypeAry {
  // Lazy expanding list of TypeAry customed to handle various Type[] lengths.
  private static final Ary<TypeAry> TYPEARY = new Ary<>(new TypeAry[1],0);
  private static Key K = new Key(null,0);

  // Wrapper to customize array.equals
  private static class Key {
    Type[] _ts;
    int _hash;
    private Key(Type[] ts, int hash) { _ts=ts; _hash = hash; }
    private static int hash( Type[] ts ) {
      int hash = 0;
      for( Type t : ts ) hash += t._hash;
      return hash;
    }
    @Override public int hashCode() { return _hash; }
    @Override public boolean equals(Object o) {
      if( !(o instanceof Key) ) return false;
      Type[] ts = ((Key)o)._ts;
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
  private Ary<Type[]> _free = new Ary<>(new Type[1][],0);
  private TypeAry( int len ) { _len=len; }

  // Make a TypeAry to handle Type[] of length 'len'
  private static TypeAry tary(int len) {
    TypeAry tary = TYPEARY.atX(len);
    return tary==null ? TYPEARY.setX(len,new TypeAry(len)) : tary;
  }

  private TypeAry check() { assert check_();  return this; }
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
  public static Type[] hash_cons(Type[] ts) { return tary(ts.length).check().hash_cons_(ts); }
  public static Type[] clone(Type[] ts) {
    Type[] ts2 = tary(ts.length).check().get();
    System.arraycopy(ts,0,ts2,0,ts.length);
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
