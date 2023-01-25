package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

import static com.cliffc.aa.AA.*;


// Program execution start
public class RootNode extends Node {
  // Inputs are:
  // [program exit control, program exit memory, program exit value, escaping RetNodes... ]
  public RootNode() { super(OP_ROOT, null, null, null); }

  @Override boolean is_CFG() { return true; }

  // Output value is:
  // [Ctrl, All_Mem_Minus_Dead, TypeRPC.ALL_CALL, escaped_fidxs, escaped_aliases,]
  @Override public TypeTuple value() {
    Node mem = in(MEM_IDX);
    Node rez = in(REZ_IDX);
    // No top-level return yet, so return most conservative answer
    if( mem == null || rez == null )
      return TypeTuple.ROOT;
    // Not sane memory
    if( !(mem._val instanceof TypeMem tmem) )
      return (TypeTuple)mem._val.oob(TypeTuple.ROOT);

    // Reset for walking
    ESCF.clear();
    EXT_ALIASES = BitsAlias.EMPTY;
    EXT_FIDXS = BitsFun.EMPTY;
    // Walk, finding escaped aliases and fidxs
    _escapes(rez._val);

    // All external aliases already escaped
    TypeMem tmem2 = TypeMem.ANYMEM;
    // All other aliases also escape
    for( int alias : EXT_ALIASES )
      tmem2 = tmem2.set(alias,tmem.at(alias));
    for( int alias : KILL_ALIASES )
      tmem2 = tmem2.set(alias,TypeStruct.UNUSED);    
    
    return TypeTuple.make(Type.CTRL,
                          tmem2,
                          TypeRPC.ALL_CALL,
                          TypeFunPtr.make(EXT_FIDXS,1),
                          TypeMemPtr.make(false,false,EXT_ALIASES,TypeStruct.ISUSED));
  }

  // Escape all Root results.  Escaping functions are called with the most
  // conservative HM-compatible arguments.  Escaping Structs are recursively
  // escaped, and can appear as input arguments.
  private static final VBitSet ESCF = new VBitSet();
  private static BitsAlias EXT_ALIASES;
  private static BitsFun EXT_FIDXS;
  private static BitsAlias KILL_ALIASES = BitsAlias.EMPTY;

  private static void _escapes(Type t) {
    if( t == Type.ALL ) {
      EXT_ALIASES = BitsAlias.NALL;
      EXT_FIDXS = BitsFun.NALL;
    }
    if( t instanceof TypeMemPtr tmp ) {
      // Add to the set of escaped structures
      for( int alias : tmp._aliases ) {
        if( alias==0 ) continue;
        if( !EXT_ALIASES.test(alias) ) continue;
        EXT_ALIASES = EXT_ALIASES.set(alias);
        //Alloc a = ALIASES.at(alias);
        //TypeMemPtr atmp = a.tmp();
        //for( TypeFld fld : atmp._obj )
        //  if( !Util.eq(fld._fld,"^") )
        //    _escapes(fld._t,work);
        throw unimpl();
      }
    }
    if( t instanceof TypeFunPtr tfp && !ESCF.tset(tfp._uid) ) {
      // Walk all escaped function args, and call them (like an external
      // Apply might) with the most conservative flow arguments possible.
      for( int fidx : tfp.fidxs() ) {
        if( fidx==0 || ESCF.tset(fidx) ) continue;
        // TODO: Lambda.apply_push
        EXT_FIDXS = EXT_FIDXS.set(fidx);
      }
      // The flow return also escapes
      _escapes(tfp._ret);
    }
  }

  static void kill_alias( int alias ) {
    if( KILL_ALIASES.test(alias) ) return;
    KILL_ALIASES = KILL_ALIASES.set(alias);
    Env.GVN.add_flow(Env.ROOT);
    CACHE_DEF_MEM = null;
  }
  private static TypeMem CACHE_DEF_MEM;
  static TypeMem def_mem() {
    if( KILL_ALIASES == BitsAlias.EMPTY ) return TypeMem.ALLMEM;
    if( CACHE_DEF_MEM!=null ) return CACHE_DEF_MEM;
    TypeMem mem = TypeMem.ALLMEM;
    for( int alias : KILL_ALIASES )
      mem = mem.set(alias,TypeStruct.UNUSED);
    return (CACHE_DEF_MEM = mem);

  }

  @Override public Type live() { return Type.ALL; }

  @Override public Node ideal_reduce() {
    // See if the result can ever refer to local memory.
    Node rez = in(REZ_IDX);
    if( rez!=null && in(MEM_IDX) != Env.XMEM &&
        !can_lift_to(rez._val,TypeMemPtr.ISUSED) &&
        !can_lift_to(rez._val,TypeFunPtr.GENERIC_FUNPTR) )
      return set_def(MEM_IDX,Env.XMEM);
    return null;
  }

  // True if t0 can lift to t1; i.e. holding t1 constant, if we strictly lift
  // t0 (so t0_new isa t0), then we can lift t0 until it is equal to t1.
  static boolean can_lift_to(Type t0, Type t1) {  return t0.join(t1)==t1;  }
  
  @Override Node walk_dom_last( Predicate<Node> P) { return null; }

  @Override public boolean has_tvar() { return false; }

  // Unify trailing result ProjNode with RootNode results; but no unification
  // with anything from Root, all results are independent.
  @Override public boolean unify_proj( ProjNode proj, boolean test ) {
    return false;
  }

  @Override public int hashCode() { return 123456789+1; }
  @Override public boolean equals(Object o) { return this==o; }

  // Reset for next test
  public void reset() {
    set_def(CTL_IDX,null);
    set_def(MEM_IDX,null);
    set_def(REZ_IDX,null);
    while( len() > REZ_IDX+1 )
      pop();
    KILL_ALIASES = BitsAlias.EMPTY;
  }
}
