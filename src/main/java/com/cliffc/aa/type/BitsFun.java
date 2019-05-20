package com.cliffc.aa.type;

import java.util.HashMap;

// Function index Bits supporting a lattice; immutable; hash-cons'd.
public class BitsFun extends Bits {
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  private static HashMap<BitsFun,BitsFun> INTERN = new HashMap<>();
  private static BitsFun FREE=null;
  @Override BitsFun make_impl(long con, long[] bits ) {
    BitsFun b1 = FREE;
    if( b1 == null ) b1 = new BitsFun();
    else FREE = null;
    b1.init(con,bits);
    BitsFun b2 = INTERN.get(b1);
    if( b2 != null ) { FREE = b1; return b2; }
    else { INTERN.put(b1,b1); return b1; }
  }

  public static final int NUL_fidx = 0;
  public static final int ALL_fidx = 1;
  static int FUN_log_reserved_fidxes = 6; // Allocate 1<<10, or a thousand reserved fidxes
  static long FUN_fidx = Bits.split_log(ALL_fidx,FUN_log_reserved_fidxes);
  static long FUN_fidx_max = FUN_fidx + (1L<<FUN_log_reserved_fidxes);
  public static long new_fidx() {
    long a = FUN_fidx++;
    assert FUN_fidx <= FUN_fidx_max;
    return a;
  }
  // Fast reset of parser state between calls to Exec
  public static int PRIM_CNT;
  public static void init0() { PRIM_CNT=(int)FUN_fidx; }
  public static void reset_to_init0() { FUN_fidx = PRIM_CNT; }
  
  // Have to make a first BitsFun here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  public static final BitsFun FULL = new BitsFun().make_impl(-2,new long[]{(1L<<NUL_fidx) | (1L<<ALL_fidx)});
  static final BitsFun ANY  = FULL.dual();
  static final BitsFun NZERO= make0(-2,new long[]{1L<<ALL_fidx});
  public static final BitsFun NIL  = make0(0);
  @Override public BitsFun FULL() { return FULL; }
  @Override public BitsFun ANY () { return ANY ; }

  static BitsFun make0( long con, long[] bits ) { return (BitsFun)FULL.make(con,bits); }
  static BitsFun make0( long... bits ) { return (BitsFun)FULL.make(bits); }
  static BitsFun make0( long bit ) { return (BitsFun)FULL.make(bit); }
  @Override public BitsFun dual() { return (BitsFun)super.dual(); }
  public BitsFun meet( BitsFun bs ) { return (BitsFun)super.meet(bs); }
  @Override public BitsFun clear(long i) { return (BitsFun)super.clear(i); }
}
