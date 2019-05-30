package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;

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

  private static final Ary<TypeTree> TREES = new Ary<>(new TypeTree[1],0);
  private static TypeTree new_fidx( TypeTree par ) { return TREES.push(new TypeTree(par,TREES._len)); }
  public static final TypeTree ALL = new_fidx(null);
  // Fast reset of parser state between calls to Exec
  public static int PRIM_CNT;
  public static void init0() { PRIM_CNT=TREES._len; }
  public static void reset_to_init0() { TypeTree.reset_to_len(TREES,PRIM_CNT); }
  
  // Have to make a first BitsFun here; thereafter the v-call to make_impl
  // will make more on demand.  But need the first one to make a v-call.
  public static final BitsFun FULL = new BitsFun().make_impl(-2,new long[]{1L | (1L<<ALL._idx)});
  private static final BitsFun ANY  = FULL.dual();
  public static final BitsFun NIL  = make0(0);
  @Override public BitsFun FULL() { return FULL; }
  @Override public BitsFun ANY () { return ANY ; }

  // Make a NEW fidx, with the given parent, and return the Bits with just it
  static BitsFun make_new_fidx( int parent_fidx ) {
    return make0(new_fidx(TREES.at(parent_fidx))._idx);
  }
  static BitsFun make0( int... bits ) { return (BitsFun)FULL.make(TREES,bits); }
  static BitsFun make0( int bit ) { return (BitsFun)FULL.make(bit); }
  @Override public BitsFun dual() { return (BitsFun)super.dual(); }
  public BitsFun meet( BitsFun bs ) { return (BitsFun)super.meet(bs,TREES); }
  @Override public BitsFun clear(int i) { return (BitsFun)super.clear(i); }
}
