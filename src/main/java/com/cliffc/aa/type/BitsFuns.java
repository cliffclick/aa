package com.cliffc.aa.type;

import com.cliffc.aa.util.*;
import java.util.Arrays;

// An AryI generified to BitsFun
public class BitsFuns extends AryI<BitsFun> {
  private static final BitsFuns BITSFUNS = new BitsFuns(-1);
  @Override Ary<AryI<BitsFun>> clinit() { return new Ary<>(new BitsFuns[1],0); }
  @Override BitsFuns make_holder(int len) { return new BitsFuns(len); }
  @Override BitsFun[] make_ary(int len) { return new BitsFun[len]; }
  @Override BitsFun[][] make_arys(int len) { return new BitsFun[len][]; }
  @Override int compute_hash(BitsFun[] ts) {
    for( BitsFun t : ts ) Util.add_hash( t._hash );
    return (int)Util.get_hash();
  }
  BitsFuns(int len) { super(len); }
  public static boolean interned(BitsFun[] ts) { return BITSFUNS._interned(ts); }
  public static final BitsFun[] EMPTY = hash_cons(get(0));


  // dual
  public static BitsFun[] dual(BitsFun[] fidxss) {
    BitsFun[] bfs = get(fidxss.length);
    for( int i=0; i<fidxss.length; i++ )
      bfs[i] = fidxss[i].dual();
    return hash_cons(bfs);
  }

  // Static forwards
  public static BitsFun[] get(int len) { return BITSFUNS._get(len); }
  public static BitsFun[] hash_cons(BitsFun[]ts) {
    return ts.length==1 && ts[0]==BitsFun.EMPTY ? EMPTY : BITSFUNS._hash_cons(ts);
  }
  public static BitsFun[] make(BitsFun t0) { return hash_cons(BITSFUNS._ts(t0)); }
}
