package com.cliffc.aa.type;

import java.util.HashMap;
// RPC Bits supporting a lattice; immutable; hash-cons'd.
public class BitsRPC extends Bits {
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  private static HashMap<BitsRPC,BitsRPC> INTERN = new HashMap<>();
  private static BitsRPC FREE=null;
  @Override BitsRPC make_impl(long con, long[] bits ) {
    BitsRPC b1 = FREE;
    if( b1 == null ) b1 = new BitsRPC();
    else FREE = null;
    b1.init(con,bits);
    BitsRPC b2 = INTERN.get(b1);
    if( b2 != null ) { FREE = b1; return b2; }
    else { INTERN.put(b1,b1); return b1; }
  }

  public static final int NUL_rpc = 0;
  public static final int ALL_rpc = 1;
  static int RPC_log_reserved_rpcs = 10; // Allocate 1<<10, or a thousand reserved RPCs
  static long RPC_rpc = Bits.split_log(ALL_rpc,RPC_log_reserved_rpcs);
  static long RPC_rpc_max = RPC_rpc + (1L<<RPC_log_reserved_rpcs);
  public static long new_rpc() {
    long a = RPC_rpc++;
    assert RPC_rpc <= RPC_rpc_max;
    return a;
  }
  // Fast reset of parser state between calls to Exec
  public static int PRIM_CNT;
  public static void init0() { PRIM_CNT=(int)RPC_rpc; }
  public static void reset_to_init0() { }
  
  // Have to make a first BitsRPC here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  static final BitsRPC FULL = new BitsRPC().make_impl(-2,new long[]{(1L<<NUL_rpc) | (1L<<ALL_rpc)});
  static final BitsRPC ANY  = FULL.dual();
  static final BitsRPC NZERO= make0(-2,new long[]{1L<<ALL_rpc});
  public static final BitsRPC NIL  = make0(0);
  @Override public BitsRPC FULL() { return FULL; }
  @Override public BitsRPC ANY () { return ANY ; }

  static BitsRPC make0( long con, long[] bits ) { return (BitsRPC)FULL.make(con,bits); }
  static BitsRPC make0( long... bits ) { return (BitsRPC)FULL.make(bits); }
  static BitsRPC make0( long bit ) { return (BitsRPC)FULL.make(bit); }
  @Override public BitsRPC dual() { return (BitsRPC)super.dual(); }
  public BitsRPC meet( BitsRPC bs ) { return (BitsRPC)super.meet(bs); }
  @Override public BitsRPC clear(long i) { return (BitsRPC)super.clear(i); }
}
