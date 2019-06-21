package com.cliffc.aa.type;

import java.util.HashMap;

// Function index Bits supporting a lattice; immutable; hash-cons'd.
public class BitsFun extends Bits<BitsFun> {
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  private static HashMap<BitsFun,BitsFun> INTERN = new HashMap<>();
  private static BitsFun FREE=null;
  @Override BitsFun make_impl(int con, long[] bits ) {
    BitsFun b1 = FREE;
    if( b1 == null ) b1 = new BitsFun();
    else FREE = null;
    b1.init(con,bits);
    BitsFun b2 = INTERN.get(b1);
    if( b2 != null ) { FREE = b1; return b2; }
    else { INTERN.put(b1,b1); return b1; }
  }

  private static final Bits.Tree<BitsFun> TREE = new Bits.Tree<>();
  @Override Tree<BitsFun> tree() { return TREE; } 
  public static final int ALL = new_fidx(0);
  public static int new_fidx( int par ) { return TREE.split(par); }
  // Fast reset of parser state between calls0 to Exec
  public static void init0() { TREE.init0(); }
  public static void reset_to_init0() { TREE.reset_to_init0(); }
  
  // Have to make a first BitsFun here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  private static final BitsFun FULL = new BitsFun().make_impl(1,new long[]{1L | (1L<<ALL)});
  private static final BitsFun ANY = FULL.dual();
  public  static final BitsFun NIL = make0(0);
  @Override boolean is_class() { return test(ALL); } // All bits are constants, except the first "ALL" bit
  @Override public BitsFun ALL() { return FULL; }
  @Override public BitsFun ANY() { return ANY ; }

  // Make a NEW fidx, with the given parent, and return the Bits with just it
  static BitsFun make_new_fidx( int parent_fidx ) { return make0(new_fidx(parent_fidx)); }
  public static BitsFun make0( int bit ) { return FULL.make(bit); }
  public static BitsFun make0( int... bits ) { return FULL.make(bits); }
  public static int last_fidx() { return TREE.last_split(); }
}
