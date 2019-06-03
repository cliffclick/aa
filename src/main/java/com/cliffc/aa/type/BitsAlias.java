package com.cliffc.aa.type;

import java.util.HashMap;

// Alias Bits supporting a lattice; immutable; hash-cons'd.
public class BitsAlias extends Bits<BitsAlias> {
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

  private static final Bits.HashMaker<BitsAlias> HASHMAKER;
  public  static final int REC;
          static final int ALL, STR;
  private static final int ARY;
  static final BitsAlias NZERO, FULL;
  static {
    HASHMAKER = new Bits.HashMaker<>();
    // The All-Memory alias class
    ALL = new_alias(0);
    NZERO = new BitsAlias().make_impl(ALL,null);
    FULL = NZERO.meet_nil(); // With a nil
    // Split All-Memory into Structs/Records and Arrays (including Strings).
    // Everything falls into one of these two camps.
    make0(REC = new_alias(ALL));
    make0(ARY = new_alias(ALL));
    // Split Arrays into Strings (and other arrays)
    make0(STR = new_alias(ARY));
  }
  public  static int new_alias(int par) { return HASHMAKER.split(par,INTERN); }
  public  static int new_string() { return new_alias(STR); }
  // Fast reset of parser state between calls to Exec
  public static void init0() { HASHMAKER.init0(); }
  public static void reset_to_init0() { HASHMAKER.reset_to_init0(); }


  // Have to make a first BitsAlias here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  private static final BitsAlias ANY  = FULL.dual();
  public static final BitsAlias NIL  = make0(0);
  @Override HashMaker hashmaker() { return HASHMAKER; }
  @Override public BitsAlias ALL() { return FULL; }
  @Override public BitsAlias ANY() { return ANY ; }

  static BitsAlias make0( int bit ) { return NZERO.make(bit); }
}
