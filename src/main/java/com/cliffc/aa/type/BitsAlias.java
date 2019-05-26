package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;

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

  static final Ary<TypeTree> TREES = new Ary<>(new TypeTree[1],1);
  public  static TypeTree new_alias(TypeTree par) { return TREES.push(new TypeTree(par,TREES._len)); }
  public  static TypeTree new_string() { return new_alias(STR); }
  public  static final TypeTree REC;
          static final TypeTree ALL, STR;
  private static final TypeTree ARY;
  static {
    // The All-Memory alias class
    ALL = new_alias(null);
    // Split All-Memory into Structs/Records and Arrays (including Strings).
    // Everything falls into one of these two camps.
    REC = new_alias(ALL);
    ARY = new_alias(ALL);
    ALL.close();
    // Split Arrays into Strings (and other arrays)
    STR = new_alias(ARY);
  }
  // Fast reset of parser state between calls to Exec
  private static int PRIM_CNT;
  public static void init0() { PRIM_CNT=TREES._len; }
  public static void reset_to_init0() { TREES.set_len(PRIM_CNT); TypeStr.reset_to_init0(); }


  // Have to make a first BitsAlias here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  static final BitsAlias FULL = new BitsAlias().make_impl(-2,new long[]{1L | (1L<<ALL._idx)});
  private static final BitsAlias ANY  = FULL.dual();
  static final BitsAlias NZERO= make0(ALL._idx);
  public static final BitsAlias NIL  = make0(0);
  @Override public BitsAlias FULL() { return FULL; }
  @Override public BitsAlias ANY () { return ANY ; }

  static BitsAlias make0( int... bits ) { return (BitsAlias)FULL.make(TREES,bits); }
  static BitsAlias make0( int bit ) { return (BitsAlias)FULL.make(bit); }
  @Override public BitsAlias dual() { return (BitsAlias)super.dual(); }
  public BitsAlias meet( BitsAlias bs ) { return (BitsAlias)super.meet(bs,TREES); }
  @Override public BitsAlias clear(int i) { return (BitsAlias)super.clear(i); }

}
