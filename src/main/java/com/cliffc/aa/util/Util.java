package com.cliffc.aa.util;

import java.util.concurrent.ConcurrentMap;

public class Util {
  // Fast linear scan for a hit, returns index or -1
  public static int find( int[] es, int e ) {
    for( int i=0; i<es.length; i++ ) if( es[i]==e ) return i;
    return -1;
  }
  // Fast linear scan for a hit, returns index or -1
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

  // Call per every get
  private static int REPROBE_CHK_CNT;
  public static void reprobe_quality_check_per(NonBlockingHashMap map) {
    if( (REPROBE_CHK_CNT++ & ((1L<<16)-1)) == 0 ) // Reports every 2^16 == 65536 gets
      reprobe_quality_check(map);
  }
  public static void reprobe_quality_check(NonBlockingHashMap map) {
    System.out.println("Reprobe histogram: "+map.reprobes());
  }
  // Call per every put
  public static void hash_quality_check_per(ConcurrentMap map) {
    if( (map.size() & ((1L<<10)-1)) == 0 ) // Reports every 2^16 == 65536 puts
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
    int[] hist = new int[32];
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
    int cnt=0;
    for( Object k : map.keySet() ) {
      int hash = k.hashCode();
      if( hash==maxkey ) {
        System.out.println("Sample: "+map.get(k));
        if( cnt++>3 ) break;
      }
    }
  }


  // Copied from http://burtleburtle.net/bob/c/lookup3.c
  // Call add_hash as many times as you like, then get_hash at the end.
  // Uses global statics, does not nest.
  private static int rot(int x, int k) { return (x<<k) | (x>>(32-k)); }
  private static int a,b,c,x;
  static public void add_hash( int h ) {
    switch( x ) {
    case 0: a+=h; x++; return;
    case 1: b+=h; x++; return;
    case 2: c+=h; x++; return;
    case 3:
      a -= c;  a ^= rot(c, 4);  c += b;
      b -= a;  b ^= rot(a, 6);  a += c;
      c -= b;  c ^= rot(b, 8);  b += a;
      a -= c;  a ^= rot(c,16);  c += b;
      b -= a;  b ^= rot(a,19);  a += c;
      c -= b;  c ^= rot(b, 4);  b += a;
      x=0;
    }
  }
  // Return the resulting hash, which is never 0
  static public int get_hash() {
    if( x!=0 ) {
      c ^= b; c -= rot(b,14);
      a ^= c; a -= rot(c,11);
      b ^= a; b -= rot(a,25);
      c ^= b; c -= rot(b,16);
      a ^= c; a -= rot(c, 4);
      b ^= a; b -= rot(a,14);
      c ^= b; c -= rot(b,24);
    }
    int hash=c;
    if( hash==0 ) hash=b;
    if( hash==0 ) hash=a;
    if( hash==0 ) hash=0xcafebabe;
    a=b=c=x=0;
    return hash;
  }
  // Single-use hash spreader
  static public int hash_spread(int hash) {
    Util.add_hash(hash);
    return Util.get_hash();
  }

  static public int gcd(int x, int y) {
    if( x==0 || y== 0 ) return 0;
    int a = Math.max(x,y), r;
    int b = Math.min(x,y);
    while((r=(a % b)) != 0) { a = b;  b = r; }
    return b;
  }

  static public boolean isUpperCase( String s ) {
    for( int i=0; i<s.length() ; i++ )
      if( !Character.isUpperCase(s.charAt(i)) )
        return false;
    return true;
  }
}
