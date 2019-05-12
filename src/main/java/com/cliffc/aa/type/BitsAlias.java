package com.cliffc.aa.type;

import java.util.HashMap;

// Alias Bits supporting a lattice; immutable; hash-cons'd.
public class BitsAlias extends Bits {
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  private static HashMap<BitsAlias,BitsAlias> INTERN = new HashMap<>();
  private static BitsAlias FREE=null;
  @Override BitsAlias make_impl(int con, long[] bits ) {
    BitsAlias b1 = FREE;
    if( b1 == null ) b1 = new BitsAlias();
    else FREE = null;
    b1.init(con,bits);
    BitsAlias b2 = INTERN.get(b1);
    if( b2 != null ) { FREE = b1; return b2; }
    else { INTERN.put(b1,b1); return b1; }
  }

  // Have to make a first BitsAlias here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  static final BitsAlias FULL = new BitsAlias().make_impl(-2,new long[]{-1});
  static final BitsAlias ANY  = FULL.dual();
  static final BitsAlias NZERO= make0(-2,new long[]{-2});
  public static final BitsAlias NIL  = make0(0);
  @Override public BitsAlias FULL() { return FULL; }
  @Override public BitsAlias ANY () { return ANY ; }

  static BitsAlias make0( int con, long[] bits ) { return (BitsAlias)FULL.make(con,bits); }
  static BitsAlias make0( int... bits ) { return (BitsAlias)FULL.make(bits); }
  static BitsAlias make0( int bit ) { return (BitsAlias)FULL.make(bit); }
  @Override public BitsAlias dual() { return (BitsAlias)super.dual(); }
  public BitsAlias meet( BitsAlias bs ) { return (BitsAlias)super.meet(bs); }
  @Override public BitsAlias clear(int i) { return (BitsAlias)super.clear(i); }

  // Individual bits can be *split* into two children bits.  The original bit
  // is lazily everywhere replaced with the children, without changing the hash
  // or equivalence properties.  A split-bit is never put into a new Bits ever
  // again, but old instances may exist until all Types are visited.  This is
  // done with a Read Barrier before any operation which walks bits (e.g. any
  // alias updates for stores/calls or debug prints) and where possible the
  // post-Read-Barrier variant replaces what was there before.

  // Entry X is 0 if bit X is unsplit; otherwise the hi/lo Short holds the two
  // split values - which are guaranteed to be larger than the unsplit bit.
  // The high 32 Int holds the parent.  Split bits form a Tree structure.
  private static long[] SPLITS = new long[1];
  // Get the numerically lower split; the next split is +1.
  // Zero means no-split, no-child
  static int get_child(int alias) { return alias < SPLITS.length ? (int)((SPLITS[alias]>>16)&0xFFFFL) : 0; }
  // Get the tree parent, or 0
  static int get_parent(int alias) { return alias < SPLITS.length ? (int)((SPLITS[alias]>>32)&0xFFFFL) : 0; }
  
  // Next bit number; max used length of SPLITS
  private static int NBITS = 0;
  public static int new_alias() { return NBITS++; }
  // Max split ever seen
  static int MAX_SPLITS = 0;
  // Read-barrier check
  BitsAlias rd_bar() { return (BitsAlias)rd_bar(SPLITS,MAX_SPLITS); }
  
  // Split this bit in twain.  Returns 2 new bits
  public static int split( int old_bit ) {
    if( old_bit > MAX_SPLITS ) MAX_SPLITS = old_bit; // Raise max split seen
    int new_bits = NBITS;        // Get 2 new bits
    NBITS += 2;
    SPLITS = Bits.split(old_bit,SPLITS,new_bits);
    return new_bits;
  }
}
