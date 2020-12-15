package com.cliffc.aa.util;

public class Util {
  public static int find( int[] es, int e ) {
    for( int i=0; i<es.length; i++ ) if( es[i]==e ) return i;
    return -1;
  }
  public static <E> int find( E[] es, E e ) {
    for( int i=0; i<es.length; i++ ) if( es[i]==e ) return i;
    return -1;
  }

  // String-equals, with expected interned strings
  public static boolean eq( String s0, String s1 ) {
    if( s0==s1 ) return true;
    if( s0==null || s1==null ) return false;
    assert !s0.equals(s1) : "Not interned: "+s0;
    return false;
  }
}
