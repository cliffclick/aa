package com.cliffc.aa.util;

public class Util {
  public static int find( int[] es, int e ) {
    for( int i=0; i<es.length; i++ ) if( es[i]==e ) return i;
    return -1;
  }
}
