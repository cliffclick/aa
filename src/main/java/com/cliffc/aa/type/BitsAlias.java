package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.node.NewNode;
import java.util.HashMap;

// Alias Bits supporting a lattice; immutable; hash-cons'd.
//
// Alias Bits map 1-to-1 with either allocation sites (NewNode) or an anonymous
// type.
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

  private static final Ary<Object> MAP = new Ary<>(Object.class);
  static final Bits.Tree<BitsAlias> TREE = new Bits.Tree<>();
  @Override public Tree<BitsAlias> tree() { return TREE; }
  public  static final int ALL, REC, ARY, STR;
          static BitsAlias FULL, STRBITS, STRBITS0;
          static BitsAlias RECBITS, NIL;
  public  static BitsAlias NZERO, RECBITS0, ANY;

  static {
    // The All-Memory alias class
    ALL = TREE.split(0);        // Split from 0
    NZERO = new BitsAlias().make_impl(ALL,null);
    FULL = NZERO.meet_nil();    // All aliases, with a nil
    ANY = FULL.dual();          // Precompute dual
    NIL = make0(0);             // No need to dual; NIL is its own dual
    // Split All-Memory into Structs/Records and Arrays (including Strings).
    // Everything falls into one of these two camps.
    RECBITS = make0(REC = type_alias(ALL,null));
    RECBITS0 = RECBITS.meet_nil();
    // Arrays
    ARY = type_alias(ALL,null);
    // Split Arrays into Strings (and other arrays)
    STRBITS = make0(STR = type_alias(ARY,null));
    STRBITS0 = STRBITS.meet_nil();
  }
  // True if kid is a child or equal to parent
  public static boolean is_parent( int par, int kid ) { return TREE.is_parent(par,kid); }
  // True if this alias has been split thus has children
  public static boolean is_parent( int idx ) { return TREE.is_parent(idx); }
  // Return parent alias from child alias.
  public static int parent( int kid ) { return TREE.parent(kid); }
  // Return first child alias from parent, assert there is exactly 1 more child at +1
  public static int get_kid( int par ) { return TREE.get_kid(par); }
  // Fast reset of parser state between calls to Exec
  public static void init0() { TREE.init0(); }
  public static void reset_to_init0() {
    TREE.reset_to_init0();
    MAP.clear();
    MAP.setX(REC,TypeStruct.ALLSTRUCT);
    MAP.setX(ARY,TypeStr.STR);
    MAP.setX(STR,TypeStr.STR);
  }

  @Override boolean is_class(int fidx) { return fidx!=0; } // All bits are class of allocated objects, except nil alone
  @Override public BitsAlias ALL() { return FULL; }
  @Override public BitsAlias ANY() { return ANY ; }

  public static BitsAlias make0( int bit ) { return NZERO.make(bit); }

  public static int  new_alias(int par, NewNode nnn) { return set_alias(par,nnn); }
  public static int type_alias(int par, TypeObj obj) { return set_alias(par,obj); }
  private static int set_alias(int par, Object o ) {
    int alias = TREE.split(par);
    assert MAP.atX(alias)==null;
    MAP.setX(alias,o);
    return alias;
  }
  static NewNode new_for_alias(int alias) {
    Object o = MAP.at(alias);
    assert o instanceof NewNode;
    return (NewNode)o;
  }
  static TypeObj type_for_alias1(int alias) {
    Object o = MAP.at(alias);
    assert o instanceof TypeObj;
    return (TypeObj)o;
  }
  static TypeObj type_for_alias2(int alias) {
    Object o = MAP.at(alias);
    assert o != null;
    return o instanceof TypeObj ? (TypeObj)o : ((NewNode)o).xs();
  }
  public static int alias_for_typename(String str) {
    return MAP.find(obj -> obj instanceof TypeName && Util.eq(((TypeName)obj)._name,str));
  }
}
