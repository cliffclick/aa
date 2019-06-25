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

  static final Bits.Tree<BitsAlias> TREE = new Bits.Tree<>();
  @Override Tree<BitsAlias> tree() { return TREE; } 
  public static final int REC, I64, F64;
  static final int ALL, STR, ABC;
  private static final int ARY;
          static BitsAlias NZERO, FULL, RECBITS0, STRBITS, STRBITS0, ABCBITS, ABCBITS0;
  public  static BitsAlias RECBITS, NIL;
  private static BitsAlias ANY;

  static {
    // The All-Memory alias class
    ALL = new_alias(0,TypeObj.OBJ);
    NZERO = new BitsAlias().make_impl(ALL,null);
    FULL = NZERO.meet_nil();    // All aliases, with a nil
    ANY = FULL.dual();          // Precompute dual
    NIL = make0(0);             // No need to dual; NIL is its own dual
    // Split All-Memory into Structs/Records and Arrays (including Strings).
    // Everything falls into one of these two camps.
    RECBITS = make0(REC = new_alias(ALL,TypeStruct.ALLSTRUCT));
    RECBITS0 = RECBITS.meet_nil();
    // Arrays
    ARY = new_alias(ALL,TypeObj.OBJ);
    // Split Arrays into Strings (and other arrays)
    STRBITS = make0(STR = new_alias(ARY,TypeStr.STR));
    STRBITS0 = STRBITS.meet_nil();
    // LibCall conversion string aliases
    I64 = new_alias(STR,TypeStr.STR);
    F64 = new_alias(STR,TypeStr.STR);
    // A sample test string
    ABCBITS = make0(ABC = new_alias(STR,TypeStr.ABC));
    ABCBITS0 = ABCBITS.meet_nil();
  }
  public static int new_alias(int par, TypeObj err_report) { return TREE.split(par,err_report); }
  // Fast reset of parser state between calls to Exec
  public static void init0() { TREE.init0(); }
  public static void reset_to_init0() { TREE.reset_to_init0();}

  // Have to make a first BitsAlias here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  @Override boolean is_class() { return abit()!=0; } // All bits are class of allocated objects, except nil alone
  @Override public BitsAlias ALL() { return FULL; }
  @Override public BitsAlias ANY() { return ANY ; }

  static BitsAlias make0( int bit ) { return NZERO.make(bit); }
}
