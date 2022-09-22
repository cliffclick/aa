package com.cliffc.aa.type;

import java.util.HashMap;

// Function index Bits supporting a lattice; immutable; hash-cons'd.

public class BitsFun extends Bits<BitsFun> {
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  private static final HashMap<BitsFun,BitsFun> INTERN = new HashMap<>();
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
  @Override public Tree<BitsFun> tree() { return TREE; }
  public static final int ALLX = new_fidx(0);
  public static final int EXTX = new_fidx(ALLX); // External callers
  public static final int INTX = new_fidx(ALLX); // Internal callers
  public static int new_fidx( int par ) { return TREE.split(par); }
  public static int new_fidx( ) { return TREE.split(INTX); } // Makes an INTERNAL fidx
  // Fast reset of parser state between calls0 to Exec
  public static void init0() { TREE.init0(); }
  public static void reset_to_init0() { TREE.reset_to_init0(); }

  // Have to make a first BitsFun here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.

  // Internal and external callers, not nil
  public  static final BitsFun NALL = new BitsFun().make_impl(ALLX,null);
  public  static final BitsFun NANY = NALL.dual();
  private static final BitsFun  ALL = NALL.make_impl(1,new long[]{0x3});
  private static final BitsFun  ANY = ALL.dual();

  public static final BitsFun EXT = make0(EXTX);
  public static final BitsFun INT = make0(INTX);
  
  public static final BitsFun EMPTY = make0();
  @Override public BitsFun ALL() { return ALL; }
  @Override public BitsFun ANY() { return ANY; }
  @Override public BitsFun EMPTY() { return EMPTY; }

  // Make a NEW fidx, with the given parent, and return the Bits with just it
  static BitsFun make_new_fidx( int parent_fidx ) { return make0(new_fidx(parent_fidx)); }
  public static void free(int fidx) { TREE.free(fidx); }
  public static BitsFun make0( int bit ) { return NALL.make(bit); }
  public static BitsFun make0( int... bits ) { return NALL.make(bits); }
  // True if this fidx has been split thus has children
  public static boolean is_parent( int idx ) { return TREE.is_parent(idx); }
  // Return parent fidx from child fidx.
  public static int parent( int kid ) { return TREE.parent(kid); }
}
