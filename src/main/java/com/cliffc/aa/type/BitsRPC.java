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

  private static final Bits.HashMaker<BitsRPC> HASHMAKER = new Bits.HashMaker<>();
  public static final int ALL = new_rpc(0);
  public static int new_rpc( int par ) { return HASHMAKER.split(par,INTERN); }
  // Fast reset of parser state between calls to Exec
  public static void init0() { HASHMAKER.init0(); }
  public static void reset_to_init0() { HASHMAKER.reset_to_init0(); }
  
  // Have to make a first BitsRPC here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  static final BitsRPC FULL = new BitsRPC().make_impl(1,new long[]{1L | (1L<<ALL)});
  private static final BitsRPC ANY = FULL.dual();
  public  static final BitsRPC NIL = make0(0);
  @Override boolean is_class() { return false; } // All bits are constants
  @Override HashMaker hashmaker() { return HASHMAKER; } 
  @Override public BitsRPC ALL() { return FULL; }
  @Override public BitsRPC ANY() { return ANY ; }

  static BitsRPC make0( int bit ) { return FULL.make(bit); }
}
