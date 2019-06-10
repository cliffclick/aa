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

          static final Bits.HashMaker<BitsAlias> HASHMAKER  = new Bits.HashMaker<>();
  public  static final int REC, I64, F64;
  static final int ALL, STR, ABC;
  private static final int ARY;
          static BitsAlias NZERO, FULL, RECBITS0, STRBITS, STRBITS0, ABCBITS, ABCBITS0;
  public  static BitsAlias RECBITS, NIL;
  private static BitsAlias ANY, EMPTY, I64BITS, F64BITS;
  private static BitsAlias[] INIT0, INITD;

  static {
    // The All-Memory alias class
    ALL = new_alias(0);
    NZERO = new BitsAlias().make_impl(ALL,null);
    NZERO.dual();               // Precompute dual
    FULL = NZERO.meet_nil();    // All aliases, with a nil
    ANY = FULL.dual();          // Precompute dual
    NIL = make0(0);             // No need to dual; NIL is its own dual
    (EMPTY = NZERO.make(false,new long[1])).dual(); // The empty alias, and dual
    // Split All-Memory into Structs/Records and Arrays (including Strings).
    // Everything falls into one of these two camps.
    (RECBITS = make0(REC = new_alias(ALL))).dual(); // Precompute
    (RECBITS0 = RECBITS.meet_nil()).dual();         // Precompute
    // Arrays
    ARY = new_alias(ALL);
    // Split Arrays into Strings (and other arrays)
    (STRBITS = make0(STR = new_alias(ARY))).dual();
    (STRBITS0 = STRBITS.meet_nil()).dual();  // Precompute
    // LibCall conversion string aliases
    (I64BITS = make0(I64 = new_alias(STR))).dual(); // Precompute
    (F64BITS = make0(F64 = new_alias(STR))).dual(); // Precompute
    // A sample test string
    (ABCBITS = make0(ABC = new_alias(STR))).dual();
    (ABCBITS0 = ABCBITS.meet_nil()).dual(); // Precompute

    INIT0 = new BitsAlias[]{FULL,NZERO,EMPTY,RECBITS,RECBITS0,STRBITS,STRBITS0,I64BITS,F64BITS,ABCBITS,ABCBITS0};
    INITD = new BitsAlias[INIT0.length];
    for( int i=0; i<INIT0.length; i++ ) INITD[i] = INIT0[i].dual();
  }
  public static int new_alias(int par) { return HASHMAKER.split(par,INTERN); }
  // Fast reset of parser state between calls to Exec
  private static int [] INIT1C;
  private static long[][] INIT1B;
  public static void init0() {
    // Assert no unknown static init BitsAlias; all are listed in INIT0.
    // Unlisted ones will not be reset, and will have a bit pattern containing
    // some old splits and will fail the basic invariants.
    assert INTERN.size()==2*INIT0.length+1; // Every starter BitsAlias and its dual
    INIT1C = new int[INIT0.length];
    INIT1B = new long[INIT0.length][];
    // Record all the initial bit-patterns, to reset them later
    for( int i=0; i<INIT0.length; i++ ) {
      INIT1C[i] = INIT0[i]._con;
      long[] bits = INIT0[i]._bits;
      INIT1B[i] = bits==null ? null : bits.clone();
    }
    HASHMAKER.init0();
  }
  public static void reset_to_init0() {
    HASHMAKER.reset_to_init0();
    INTERN.clear();
    INTERN.put(NIL,NIL);
    // Reset all bit patterns
    for( int i=0; i<INIT0.length; i++ ) {
      BitsAlias ba = INIT0[i];
      ba._con = INIT1C[i];
      long[] bits = INIT1B[i];
      ba._bits = bits==null ? null : bits.clone();
      assert ba._hash == HASHMAKER.compute_hash(ba);
      INTERN.put(ba,ba);
      // Duals
      BitsAlias d = INITD[i];
      d._con = -INIT1C[i];
      d._bits = ba._bits;
      d._hash = ba._hash;
      assert d._hash == HASHMAKER.compute_hash(d);
      INTERN.put(d,d);
    }
  }


  // Have to make a first BitsAlias here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  @Override boolean is_class() { return true; } // All bits are class of allocated objects
  @Override HashMaker hashmaker() { return HASHMAKER; }
  @Override public BitsAlias ALL() { return FULL; }
  @Override public BitsAlias ANY() { return ANY ; }

  static BitsAlias make0( int bit ) { return NZERO.make(bit); }
}
