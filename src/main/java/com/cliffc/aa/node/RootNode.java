package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.AryInt;
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
    // Conservative final result
    Node rez = in(REZ_IDX);
    if( rez==null ) return TypeTuple.ROOT;
    Type trez = rez._val;
    // Conservative final memory
    Node mem = in(MEM_IDX);
    TypeMem tmem = mem._val instanceof TypeMem tmem0 ? tmem0 : mem._val.oob(TypeMem.ALLMEM);
    // All external aliases already escaped
    tmem = tmem.set(BitsAlias.EXTX,TypeStruct.ISUSED);
    
    // Reset for walking
    // Walk, finding escaped aliases and fidxs
    escapes_reset(tmem);
    escapes(trez);

    // Kill the killed
    for( int alias : KILL_ALIASES )
      EXT_MEM = EXT_MEM.set(alias,TypeStruct.UNUSED);

    return TypeTuple.make(Type.CTRL,
                          EXT_MEM,
                          TypeRPC.ALL_CALL,
                          TypeFunPtr.make(EXT_FIDXS,1),
                          TypeMemPtr.make(false,false,EXT_ALIASES,TypeStruct.ISUSED));
  }

  // Escape all Root results.  Escaping functions are called with the most
  // conservative HM-compatible arguments.  Escaping functions update the
  // global memory state, and their return has to be visited also.

  // Escaping pointers escape their structs, including their fields.  Escaping
  // Structs state is pulled from the global memory state.  Struct fields can
  // include new escaping functions, which bring in new memory state.

  // This cycle fcn->mem->ptr->struct->fcn requires a worklist algo.
  
  private static final VBitSet VISIT = new VBitSet();
  private static final AryInt ALIASES = new AryInt();
  // Results computed here, and modified at each call.
  static BitsAlias EXT_ALIASES;
  static BitsFun   EXT_FIDXS  ;
  static TypeMem   EXT_MEM    ;

  static void escapes_reset(TypeMem tmem) {
    VISIT.clear();
    ALIASES.clear();
    EXT_ALIASES = BitsAlias.EMPTY;
    EXT_FIDXS   = BitsFun  .EMPTY;
    EXT_MEM = tmem; // Root: TypeMem.ANYMEM.set(BitsAlias.EXTX,TypeStruct.ISUSED);    
  }
  
  static void escapes( Type t ) {
    _escapes(t);
    while( !ALIASES.isEmpty() )
      _escapes(EXT_MEM.at(ALIASES.pop()));
  }
  private static void _escapes( Type t ) {
    if( VISIT.tset(t._uid) ) return;
    if( t == TypeNil.SCALAR || t == TypeNil.NSCALR ) {
      EXT_ALIASES = BitsAlias.NALL;
      EXT_FIDXS   = BitsFun  .NALL;
    }
    if( t instanceof TypeMemPtr tmp ) {
      if( tmp._aliases == BitsAlias.NALL ) return;
      // Add to the set of escaped structures
      for( int alias : tmp._aliases )
        if( !EXT_ALIASES.test(alias) ) { // Never seen before escape
          assert !KILL_ALIASES.test(alias);
          EXT_ALIASES = EXT_ALIASES.set(alias);
          ALIASES.push(alias);
        }
    }
    if( t instanceof TypeFunPtr tfp ) {
      if( tfp.fidxs() == BitsFun.NALL ) return;
      // Walk all escaped function args, and call them (like an external
      // Apply might) with the most conservative flow arguments possible.
      for( int fidx : tfp.fidxs() ) {
        if( !EXT_FIDXS.test(fidx) ) {
          EXT_FIDXS = EXT_FIDXS.set(fidx);
          RetNode ret = RetNode.get(fidx);
          if( ret != null && ret._val instanceof TypeTuple rtup ) {
            ret.deps_add(Env.ROOT);
            TypeMem rmem = (TypeMem)rtup.at(MEM_IDX);
            TypeMem tmem2 = (TypeMem)rmem.meet(EXT_MEM);
            for( int xalias : EXT_ALIASES )
              if( EXT_MEM.at(xalias) != tmem2.at(xalias) &&
                  ALIASES.find(xalias)!= -1 )
                ALIASES.push(xalias); // Revisit
            EXT_MEM = tmem2;
          }
        }
      }
      // The return also escapes
      _escapes(tfp._ret);
    }
    // Structs escape all public fields
    if( t instanceof TypeStruct ts )
      for( TypeFld fld : ts )
        // Root widens all non-final fields
        _escapes(fld._access== TypeFld.Access.Final ? fld._t : TypeNil.SCALAR);
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
        cannot_lift_to(rez._val,TypeMemPtr.ISUSED) &&
        cannot_lift_to(rez._val,TypeFunPtr.GENERIC_FUNPTR) )
      return set_def(MEM_IDX,Env.XMEM);
    return null;
  }

  // True if t0 can lift to t1; i.e. holding t1 constant, if we strictly lift
  // t0 (so t0_new isa t0), then we can lift t0 until it is equal to t1.
  static boolean cannot_lift_to(Type t0, Type t1) {
    Type mt = t0.meet(t1);
    return !(t0==mt || t1==mt);
  }
  
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
