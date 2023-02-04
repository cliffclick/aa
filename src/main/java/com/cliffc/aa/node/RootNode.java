package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

import static com.cliffc.aa.AA.*;


// Program execution start
public class RootNode extends Node {
  // Inputs are:
  // [program exit control, program exit memory, program exit value, escaping RetNodes... ]
  public RootNode() { super(OP_ROOT, null, null, null); }

  @Override boolean is_CFG() { return true; }

  TypeMem rmem() {
    return _val instanceof TypeTuple tt ? (TypeMem)tt.at(MEM_IDX) : TypeMem.ALLMEM.oob(_val.above_center());
  }
  BitsAlias ralias() {
    return _val instanceof TypeTuple tt
      ? ((TypeMemPtr)tt.at(4))._aliases
      : (_val.above_center() ? BitsAlias.NALL.dual() : BitsAlias.NALL);
  }
  BitsFun rfidxs() {
    return _val instanceof TypeTuple tt
      ? ((TypeFunPtr)tt.at(3)).fidxs()
      : (_val.above_center() ? BitsFun.NALL.dual() : BitsFun.NALL);
  }

  
  // Output value is:
  // [Ctrl, All_Mem_Minus_Dead, TypeRPC.ALL_CALL, escaped_fidxs, escaped_aliases,]
  @Override public TypeTuple value() {
    // Conservative final memory
    Node mem = in(MEM_IDX);
    TypeMem tmem = mem!=null && mem._val instanceof TypeMem tmem0 ? tmem0 : TypeMem.ALLMEM;
    // Conservative final result
    Node rez = in(REZ_IDX);
    Type trez = rez!=null ? rez._val : Type.ALL;

    // Reset for walking
    // Walk, finding escaped aliases and fidxs
    escapes_reset();
    escapes(trez, tmem);

    TypeMem tmem2 = TypeMem.ANYMEM;
    // All external aliases already escaped
    tmem2 = tmem2.set(BitsAlias.EXTX,TypeStruct.ISUSED);
    // All escaped functions are called inside of Root, and modify memory "off-line".
    if( EXT_FIDXS != BitsFun.NALL )
      for( int fidx : EXT_FIDXS ) {
        RetNode ret = RetNode.get(fidx);
        if( ret != null && ret._val instanceof TypeTuple rtup ) {
          TypeMem rmem = (TypeMem)rtup.at(MEM_IDX);
          tmem2 = (TypeMem)tmem2.meet(rmem);
          ret.deps_add(this);   // Ret changes, so do we
        }
      }
    else tmem2 = TypeMem.ALLMEM;
    // Root changes all escaping *internal* aliases for modifiable fields
    for( int alias : EXT_ALIASES ) {
      TypeStruct ts = tmem2.at(alias);
      TypeStruct ts_wide = ts.widen_mut_fields();
      tmem2 = tmem2.set(alias, ts_wide);
    }
    // Kill the killed
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
  private static final VBitSet VISIT = new VBitSet();
  // Results computed here, and modified at each call.
  static BitsAlias EXT_ALIASES;
  static BitsFun   EXT_FIDXS  ;

  static void escapes_reset() {
    VISIT.clear();
    EXT_ALIASES = BitsAlias.EMPTY;
    EXT_FIDXS   = BitsFun  .EMPTY;
  }
  
  static void escapes(Type t, TypeMem tmem ) {
    if( VISIT.tset(t._uid) ) return;
    if( t == Type.ALL ) {
      // Escaping everything
      EXT_ALIASES = BitsAlias.NALL;
      EXT_FIDXS   = BitsFun  .NALL;
    }
    if( t instanceof TypeMemPtr tmp ) {
      // Add to the set of escaped structures
      for( int alias : tmp._aliases ) {
        EXT_ALIASES = EXT_ALIASES.set(alias);
        if( tmem!=null ) {
          TypeStruct ts = tmem.at(alias);
          //escapes(ts._def,tmem);
          for( TypeFld fld : ts )
            escapes(fld._t,tmem);
        } else 
          throw unimpl();
      }
    }
    if( t instanceof TypeFunPtr tfp ) {
      // Walk all escaped function args, and call them (like an external
      // Apply might) with the most conservative flow arguments possible.
      for( int fidx : tfp.fidxs() )
        EXT_FIDXS = EXT_FIDXS.set(fidx);
      // The return also escapes
      escapes(tfp._ret,tmem);
    }
  }

  // Given a TV3, mimic a matching flow Type from all possible escaping
  // aliases.  Escaped functions might be called with these aliases.
  public BitsAlias matching_escaped_aliases(TV3 tv3, Node dep) {
    // Caller result depends on escaping fidxs
    if( dep!=null ) deps_add(dep);
    BitsAlias aliases = BitsAlias.EMPTY;
    for( int alias : ralias() )
      if( tv3.trial_unify_ok(NewNode.get(alias).tvar(),false) )
        aliases = aliases.set(alias); // Compatible escaping alias
    return aliases;
  }

  static private final Ary<FunNode> EXT_FUNS_BY_NARGS = new Ary<>(new FunNode[1],0);
  // Given a TV3 lam, mimic a matching flow TypeFunPtr from all possible
  // escaping fidxs.  Escaped functions might be called from Root.
  public BitsFun matching_escaped_fidxs(TVLambda lam, Node dep) {
    // Caller result depends on escaping fidxs
    if( dep!=null ) deps_add(dep);
    BitsFun fidxs = BitsFun.EMPTY;
    // Toss in a generic nargs-correct external function which has !_is_copy.
    FunNode fun = EXT_FUNS_BY_NARGS.atX(lam.nargs());
    if( fun==null )
      EXT_FUNS_BY_NARGS.setX(lam.nargs(),fun=new FunNode(" generic external lambda",BitsFun.new_fidx(BitsFun.EXTX),lam.nargs()));
    fidxs = fidxs.set(fun._fidx);
    // Cannot ask for trial_unify_ok until HM_FREEZE, because trials can fail
    // over time which runs the result backwards in GCP.
    if( Combo.HM_FREEZE )
      for( int fidx : rfidxs() ) {
        RetNode ret = RetNode.get(fidx);
        if( ret != null ) {     // External function, no real sig or def
          TV3 funtvar = ret.funptr().tvar();
          if( funtvar instanceof TVLambda esc_lam && lam.trial_unify_ok(esc_lam,false) )
            fidxs = fidxs.set(fidx); // Compatible escaping fidx
        }
      }
    return fidxs;
  }
  
  private static BitsAlias KILL_ALIASES = BitsAlias.EMPTY;
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
  static boolean can_lift_to(Type t0, Type t1) {  return t0.join(t1)==t0;  }
  
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
