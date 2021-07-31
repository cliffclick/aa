package com.cliffc.aa.util;

import java.util.concurrent.ConcurrentMap;

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

  // Call per every put
  public static void hash_quality_check_per(ConcurrentMap map) {
    if( (map.size() & ((1L<<16)-1)) == 0 ) // Reports every 2^16 == 65536 puts
      hash_quality_check(map);
  }
  // Call for a report
  public static void hash_quality_check(ConcurrentMap map) {
    NonBlockingHashMapLong<Integer> hashs = new NonBlockingHashMapLong<>();
    for( Object k : map.keySet() ) {
      int hash = k.hashCode();
      Integer ii = hashs.get(hash);
      hashs.put(hash,ii==null ? 1 : ii+1);
    }
    int[] hist = new int[16];
    int maxval=0;
    long maxkey=-1;
    for( long l : hashs.keySet() ) {
      int reps = hashs.get(l);
      if( reps > maxval ) { maxval=reps; maxkey=l; }
      if( reps < hist.length ) hist[reps]++;
      else System.out.println("hash "+l+" repeats "+reps);
    }
    for( int i=0; i<hist.length; i++ )
      if( hist[i] > 0 )
        System.out.println("Number of hashes with "+i+" repeats: "+hist[i]);
    System.out.println("Max repeat key "+maxkey+" repeats: "+maxval);
  }
}
