package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.IHashMap;

// Class to make hashcons Type[].
// Bug to change after interning.
public class TypeFlds {
  // Lazy expanding list of TypeAry customed to handle various Type[] lengths.
  private static final Ary<TypeFlds> TYPEARY = new Ary<>(new TypeFlds[1],0);

  // Make a TypeAry to handle Type[] of length 'len'
  private static TypeFlds tary( int len) {
    TypeFlds tary = TYPEARY.atX(len);
    return tary==null ? TYPEARY.setX(len,new TypeFlds(len)) : tary;
  }

  private static final Key K = new Key(null,0);

  // Wrapper to customize array.equals
  private static class Key {
    TypeFld[] _ts;
    int _hash;
    private Key(TypeFld[] ts, int hash) { _ts=ts; _hash = hash; }
    private static int hash( Type[] ts ) {
      int hash = 0;
      for( Type t : ts ) hash += t._hash;
      return hash;
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
  private final Ary<TypeFld[]> _free = new Ary<>(new TypeFld[1][],0);
  private TypeFlds( int len ) { _len=len; }

  private boolean check_(TypeFld[] ts) {
    K._ts=ts;
    K._hash = Key.hash(ts);
    Key k2 = _intern.get(K);
    return k2._ts==ts;
  }


  // Return a free Type[]
  private TypeFld[] get() {
    if( _free.isEmpty() )
      _free.push(new TypeFld[_len]);
    return _free.pop();
  }

  private TypeFld[] hash_cons_(TypeFld[] ts) {
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



  public static TypeFld[] get(int len) { return tary(len).get(); }
  public static void free(TypeFld[] ts) { tary(ts.length)._free.push(ts); }
  public static TypeFld[] hash_cons(TypeFld[] ts) { return tary(ts.length).hash_cons_(ts); }
  public static TypeFld[] ts(TypeFld t0) {
    TypeFlds t1 = tary(1);
    TypeFld[] ts = t1.get();
    ts[0] = t0;
    return ts;
  }
  public static TypeFld[] ts(TypeFld t0, TypeFld t1) {
    TypeFlds t2 = tary(2);
    TypeFld[] ts = t2.get();
    ts[0] = t0;
    ts[1] = t1;
    return ts;
  }
  public static TypeFld[] ts(TypeFld t0, TypeFld t1, TypeFld t2) {
    TypeFlds t3 = tary(3);
    TypeFld[] ts = t3.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    return ts;
  }
  public static TypeFld[] ts(TypeFld t0, TypeFld t1, TypeFld t2, TypeFld t3) {
    TypeFlds t4 = tary(4);
    TypeFld[] ts = t4.get();
    ts[0] = t0;
    ts[1] = t1;
    ts[2] = t2;
    ts[3] = t3;
    return ts;
  }

  // Result not interned; suitable for direct hacking.
  // All TypeFlds are cloned new, not-interned and suitable for direct hacking.
  // Original assumed in-use, not freed.
  public static TypeFld[] clone(TypeFld[] ts) {
    TypeFld[] ts2 = tary(ts.length).get();
    for( int i=0; i<ts.length; i++ )
      ts2[i] = TypeFld.malloc(ts[i]._fld,ts[i]._t,ts[i]._access,ts[i]._order);
    return ts2;
  }

  // Result not interned; suitable for direct hacking.
  public static TypeFld[] copyOf(TypeFld[] flds, int len) {
    TypeFld[] flds2 = tary(len).get();
    System.arraycopy(flds,0,flds2,0,Math.min(flds.length,len));
    return flds2;
  }
}
