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

  private static int CNT;
  public static TypeTree new_alias(TypeTree par) { return new TypeTree(par,CNT++); }
  public static TypeTree new_string() { return new TypeTree(STR,CNT++); }
  public static final TypeTree NUL, ALL, REC, ARY, STR, ABC;
  public static final int NUL_alias;
  static {
    NUL = new_alias(null);
    NUL_alias = NUL._idx;
    // The All-Memory alias class
    ALL = new_alias(null);
    // Split All-Memory into Structs/Records and Arrays (including Strings).
    // Everything falls into one of these two camps.
    REC = new_alias(ALL);
    ARY = new_alias(ALL);
    ALL.close();
    // Split Arrays into Strings (and other arrays)
    STR = new_alias(ARY);
    // Split a few constant test Strings out
    ABC = new_string();
  }
  // Fast reset of parser state between calls to Exec
  public static int PRIM_CNT;
  public static void init0() { PRIM_CNT=CNT; }
  public static void reset_to_init0() { CNT = PRIM_CNT; }


  // Have to make a first BitsAlias here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  static final BitsAlias FULL = new BitsAlias().make_impl(-2,new long[]{(1L<<NUL_alias) | (1L<<ALL._idx)});
  static final BitsAlias ANY  = FULL.dual();
  static final BitsAlias NZERO= make0(-2,new long[]{1L<<ALL._idx});
  public static final BitsAlias NIL  = make0(0);
  @Override public BitsAlias FULL() { return FULL; }
  @Override public BitsAlias ANY () { return ANY ; }

  static BitsAlias make0( int con, long[] bits ) { return (BitsAlias)FULL.make(con,bits); }
  static BitsAlias make0( int... bits ) { return (BitsAlias)FULL.make(bits); }
  static BitsAlias make0( int bit ) { return (BitsAlias)FULL.make(bit); }
  @Override public BitsAlias dual() { return (BitsAlias)super.dual(); }
  public BitsAlias meet( BitsAlias bs ) { return (BitsAlias)super.meet(bs); }
  @Override public BitsAlias clear(int i) { return (BitsAlias)super.clear(i); }

}
