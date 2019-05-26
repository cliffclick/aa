package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;

import java.util.HashMap;

// RPC Bits supporting a lattice; immutable; hash-cons'd.
public class BitsRPC extends Bits {
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  private static HashMap<BitsRPC,BitsRPC> INTERN = new HashMap<>();
  private static BitsRPC FREE=null;
  @Override BitsRPC make_impl(int con, long[] bits ) {
    BitsRPC b1 = FREE;
    if( b1 == null ) b1 = new BitsRPC();
    else FREE = null;
    b1.init(con,bits);
    BitsRPC b2 = INTERN.get(b1);
    if( b2 != null ) { FREE = b1; return b2; }
    else { INTERN.put(b1,b1); return b1; }
  }

  public static final Ary<TypeTree> TREES = new Ary<>(new TypeTree[1],0);
  public static TypeTree new_rpc(TypeTree par) { return TREES.push(new TypeTree(par,TREES._len)); }
  // Make a NEW RPC, with the given parent index
  public static int make_new_rpc( int parent_rpc ) { return new_rpc(TREES.at(parent_rpc))._idx; }
  public static final TypeTree ALL = new_rpc(null);
  // Fast reset of parser state between calls to Exec
  public static int PRIM_CNT;
  public static void init0() { PRIM_CNT=TREES._len; }
  public static void reset_to_init0() { TREES.set_len(PRIM_CNT); }
  
  // Have to make a first BitsRPC here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  static final BitsRPC FULL = new BitsRPC().make_impl(-2,new long[]{(1L<<0) | (1L<<ALL._idx)});
  static final BitsRPC ANY  = FULL.dual();
  static final BitsRPC NZERO= make0(ALL._idx);
  public static final BitsRPC NIL  = make0(0);
  @Override public BitsRPC FULL() { return FULL; }
  @Override public BitsRPC ANY () { return ANY ; }

  static BitsRPC make0( int... bits ) { return (BitsRPC)FULL.make(bits); }
  static BitsRPC make0( int bit ) { return (BitsRPC)FULL.make(bit); }
  @Override public BitsRPC dual() { return (BitsRPC)super.dual(); }
  public BitsRPC meet( BitsRPC bs ) { return (BitsRPC)super.meet(bs); }
  @Override public BitsRPC clear(int i) { return (BitsRPC)super.clear(i); }
}
