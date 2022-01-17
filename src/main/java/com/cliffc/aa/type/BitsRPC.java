package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;

import java.util.HashMap;

// RPC Bits supporting a lattice; immutable; hash-cons'd.
public class BitsRPC extends Bits<BitsRPC> {
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

  private static final Bits.Tree<BitsRPC> TREE = new Bits.Tree<>();
  @Override Tree<BitsRPC> tree() { return TREE; } 
  public static final int ALLX = new_rpc(0);
  public static int new_rpc( int par ) { return TREE.split(par); }
  // Fast reset of parser state between calls to Exec
  public static void init0() { TREE.init0(); }
  public static void reset_to_init0() { TREE.reset_to_init0(); }
  
  // Have to make a first BitsRPC here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  static final BitsRPC ALL0 = new BitsRPC().make_impl(1,new long[]{1L | (1L<<ALLX)});
  private static final BitsRPC ANY0 = ALL0.dual();
  public  static final BitsRPC NIL = make0(0);
  public static final BitsRPC EMPTY = ALL0.make(); // No bits
  @Override public BitsRPC ALL0() { return ALL0; }
  @Override public BitsRPC ANY0() { return ANY0; }
  @Override public BitsRPC EMPTY() { return EMPTY ; }

  static BitsRPC make0( int bit ) { return ALL0.make(bit); }
}
