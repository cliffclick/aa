package com.cliffc.aa.type;

import com.cliffc.aa.util.*;
import java.util.Arrays;

// Class to make hash-cons TypeFld[].  Fields are unordered - so really
// alpha-sorted to be canonical.  Bug to change after interning.
public class TypeFlds {
  // Lazy expanding list of Ary<TypeFld> customized to handle various TypeFld[] lengths.
  private static final Ary<TypeFlds> TYPEARY = new Ary<>(new TypeFlds[1],0);

  private static final TypeFld DEAD = null;

  // Make a Ary<Type> to handle Type[] of length 'len'
  private static TypeFlds tary( int len) {
    TypeFlds tary = TYPEARY.atX(len);
    return tary==null ? TYPEARY.setX(len,new TypeFlds(len)) : tary;
  }

  private static final Key K = new Key(null,0);

  public static final TypeFld[] EMPTY = hash_cons(get(0));

  // Wrapper to customize array.equals
  private static class Key {
    TypeFld[] _ts;
    int _hash;
    private Key(TypeFld[] ts, int hash) {
      _ts=ts;
      _hash = hash;
      // Only handed sorted fields
      if( ts!=null )
        for( int i=0; i<ts.length-1; i++ )
          assert sbefore(ts[i]._fld,ts[i+1]._fld);
    }
    private static int hash( TypeFld[] ts ) {
      for( Type t : ts ) Util.add_hash( t._hash);
      return (int)Util.get_hash();
    }
    @Override public int hashCode() { return _hash; }
    @Override public boolean equals(Object o) {
      if( !(o instanceof Key key) ) return false;
      TypeFld[] ts = key._ts;
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
  // Are the fields in order?
  public static boolean sbefore(String s0, String s1) {
    if( Util.eq(s0,"^") ) return true;
    if( Util.eq(s1,"^") ) return false;
    return s0.compareTo(s1) < 0;
  }

  private int _cnt;             // Count of new allocations
  private final int _len;       // Length of arrays being handled
  private final IHashMap _intern = new IHashMap();
  private final Ary<TypeFld[]> _free = new Ary<>(new TypeFld[1][],0);
  private TypeFlds( int len ) { _len=len; }

  // Return a free TypeFld[]
  private TypeFld[] get() {
    if( _free.isEmpty() ) {
      _cnt++;  assert _cnt<1000;
      _free.push(new TypeFld[_len]);
    }
    return _free.pop();
  }

  private TypeFld[] hash_cons_(TypeFld[] ts) {
    if( Type.RECURSIVE_MEET > 0 ) {
      if( !check(ts) ) return ts; // Cannot intern yet
    } else assert check(ts);
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
  private boolean check(TypeFld[]ts) {
    for( TypeFld fld : ts )
      if( fld.un_interned() )
        return false;
    return true;
  }
  private boolean interned_(TypeFld[] ts) {
    K._ts=ts;
    K._hash = Key.hash(ts);
    Key k2 = _intern.get(K);
    return k2!=null && k2._ts==ts;
  }

  public static TypeFld[] get(int len) { return tary(len).get(); }
  public static void free(TypeFld[] ts) {
    Arrays.fill(ts,null);
    if( ts.length>0 ) ts[0] = DEAD;
    tary(ts.length)._free.push(ts);
  }
  public static TypeFld[] hash_cons(TypeFld[] ts) { return tary(ts.length).hash_cons_(ts); }
  public static boolean   interned (TypeFld[] ts) { return tary(ts.length).interned_ (ts); }

  // Result not interned; suitable for direct hacking.
  // Original assumed in-use, not freed.
  public static TypeFld[] clone(TypeFld[] ts) {
    TypeFld[] ts2 = tary(ts.length).get();
    System.arraycopy(ts,0,ts2,0,ts.length);
    return ts2;
  }
  // Result not interned; suitable for direct hacking.
  // Original assumed in-use, not freed.
  public static TypeFld[] copyOf(TypeFld[] ts, int len) {
    TypeFld[] ts2 = tary(len).get();
    int minlen = Math.min(len,ts.length);
    System.arraycopy(ts,0,ts2,0,minlen);
    Arrays.fill(ts2,minlen,len,null);
    return ts2;
  }
  public static boolean eq( TypeFld[] ts0, TypeFld[] ts1 ) {
    if( ts0==ts1 ) return true;
    if( ts0==null || ts1==null ) return false;
    assert !_eq(ts0,ts1);       // Check: Pointer-eq === deep-eq Arrays
    return false;               // No need for deep check, since interned
  }
  private static boolean _eq( TypeFld[] ts0, TypeFld[] ts1 ) {
    if( ts0.length!=ts1.length ) return false;
    for( int i=0; i<ts0.length; i++ )
      if( ts0[i]!=ts1[i] ) return false;
    return true;
  }

  // Make a 1-field TypeFlds
  public static TypeFld[] make(TypeFld fld) {
    TypeFld[] tfs = get(1);
    tfs[0] = fld;
    return hash_cons(tfs);
  }
  // Make a 2-field TypeFlds
  public static TypeFld[] make(TypeFld fld0, TypeFld fld1) {
    TypeFld[] tfs = get(2);
    tfs[0] = fld0;
    tfs[1] = fld1;
    return hash_cons(tfs);
  }
  // Make a 3-field TypeFlds
  public static TypeFld[] make(TypeFld fld0, TypeFld fld1, TypeFld fld2) {
    TypeFld[] tfs = get(3);
    tfs[0] = fld0;
    tfs[1] = fld1;
    tfs[2] = fld2;
    return hash_cons(tfs);
  }

  // Does not hash-cons
  public static TypeFld[] make_from(TypeFld[] flds, int idx, TypeFld fld) {
    TypeFld[] tfs = flds.clone();
    tfs[idx] = fld;
    return tfs;
  }

  // Append a field.  Preserve alpha order.  Does not hash-cons.
  public static TypeFld[] add(TypeFld[] flds, TypeFld fld) {
    TypeFld[] fs = copyOf(flds,flds.length+1);
    fs[flds.length]=fld;
    int i=0;
    while( i<flds.length && sbefore(flds[i]._fld,fld._fld) ) i++;
    fs[i]=fld;
    System.arraycopy(flds,i,fs,i+1,flds.length-i);
    return fs;
  }
}
