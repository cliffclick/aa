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
  @Override public boolean is_mem() { return true; }

  TypeMem rmem() {
    return _val instanceof TypeTuple tt ? (TypeMem)tt.at(MEM_IDX) : TypeMem.ALLMEM.oob(_val.above_center());
  }
  public BitsAlias ralias() {
    return _val instanceof TypeTuple tt
      ? ((TypeNil)tt.at(3))._aliases
      : (_val.above_center() ? BitsAlias.NALL.dual() : BitsAlias.NALL);
  }
  public BitsFun rfidxs() {
    return _val instanceof TypeTuple tt
      ? ((TypeNil)tt.at(3))._fidxs
      : (_val.above_center() ? BitsFun.NALL.dual() : BitsFun.NALL);
  }
  public TypeNil ext_scalar() {
    return (TypeNil)(_val instanceof TypeTuple tt
                        ? tt.at(3)
                        : _val.oob(TypeNil.INTERNAL));
  }

  
  // Output value is:
  // [Ctrl, All_Mem_Minus_Dead, TypeRPC.ALL_CALL, escaped_fidxs, escaped_aliases,]
  @Override public TypeTuple value() {
    // Conservative final result
    Node rez = in(REZ_IDX);
    if( rez==null ) return TypeTuple.make(Type.CTRL,def_mem(this),TypeRPC.ALL_CALL,TypeNil.SCALAR);
    Type trez = rez._val;
    // Conservative final memory
    Node mem = in(MEM_IDX);
    TypeMem tmem = mem._val instanceof TypeMem tmem0 ? tmem0 : mem._val.oob(TypeMem.ALLMEM);
    // All external aliases already escaped
    tmem = tmem.set(BitsAlias.EXTX,TypeStruct.ISUSED);
    
    // Reset for walking
    // Walk, finding escaped aliases and fidxs
    escapes_reset(tmem);
    escapes(trez,this);

    // Roots value is all reachable alias memory shapes, plus all reachable
    // (escaped) aliases and functions.
    return TypeTuple.make(Type.CTRL,
                          EXT_MEM,
                          TypeRPC.ALL_CALL,
                          TypeNil.make(false,false,false,
                                       EXT_ALIASES.meet(BitsAlias.EXT),
                                       EXT_FIDXS  .meet(BitsFun  .EXT)));
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
    EXT_MEM = tmem;
    // Kill the killed
    for( int alias : KILL_ALIASES )
      EXT_MEM = EXT_MEM.set(alias,TypeStruct.UNUSED);
  }
  
  static void escapes( Type t, Node dep ) {
    _escapes(t,dep);
    while( !ALIASES.isEmpty() )
      _escapes(EXT_MEM.at(ALIASES.pop()),dep);
  }
  private static void _escapes( Type t, Node dep ) {
    if( VISIT.tset(t._uid) ) return;
    if( !(t instanceof TypeNil tn) ) return;
    
    if( tn._aliases != BitsAlias.NALL && !tn._aliases.above_center() ) {
      // Add to the set of escaped aliases
      for( int alias : tn._aliases )
        if( !EXT_ALIASES.test(alias) ) { // Never seen before escape
          assert !KILL_ALIASES.test(alias);
          EXT_ALIASES = EXT_ALIASES.set(alias);
          ALIASES.push(alias);
        }
    }

    if( tn._fidxs != BitsFun.NALL && !tn._fidxs.above_center() ) {
      // Walk all escaped function args, and call them (like an external
      // Apply might) with the most conservative flow arguments possible.
      for( int fidx : tn._fidxs ) {
        if( !EXT_FIDXS.test(fidx) ) { // Never seen before escape
          EXT_FIDXS = EXT_FIDXS.set(fidx);
          RetNode ret = RetNode.get(fidx);
          if( ret != null && ret._val instanceof TypeTuple rtup ) {
            ret.deps_add(dep);
            TypeMem tmem2 = (TypeMem)rtup.at(MEM_IDX).meet(EXT_MEM);
            for( int xalias : EXT_ALIASES )
              if( EXT_MEM.at(xalias) != tmem2.at(xalias) &&
                  ALIASES.find(xalias)!= -1 )
                ALIASES.push(xalias); // Revisit
            EXT_MEM = tmem2;
          }
        }
      }
      // The return also escapes
      if( tn instanceof TypeFunPtr tfp )
        _escapes(tfp._ret,dep);
    }
    // Structs escape all public fields
    if( t instanceof TypeStruct ts )
      for( TypeFld fld : ts )
        // Root widens all non-final fields
        _escapes(fld._access== TypeFld.Access.Final ? fld._t : TypeNil.SCALAR,dep);
  }

  // Given a TV3, mimic a matching flow Type from all possible escaping
  // aliases.  Escaped functions might be called with these aliases.
  public BitsAlias matching_escaped_aliases(TV3 tv3, Node dep) {
    // Caller result depends on escaping fidxs
    if( dep!=null ) deps_add(dep);
    BitsAlias ralias = ralias();
    if( ralias==BitsAlias.NALL ) return BitsAlias.NALL;
    BitsAlias aliases = BitsAlias.EMPTY;
    for( int alias : ralias() )
      if( alias>3 && tv3.trial_unify_ok(NewNode.get(alias).tvar(),false) )
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

  // Default memory during initial Iter, before Combo: all memory minus the
  // kills.  Many things produce def_mem, and in general it has to be used
  // until Combo finishes the Call Graph.
  private static BitsAlias KILL_ALIASES = BitsAlias.EMPTY;
  static void kill_alias( int alias ) {
    if( KILL_ALIASES.test(alias) ) return;
    KILL_ALIASES = KILL_ALIASES.set(alias);
    CACHE_DEF_MEM = CACHE_DEF_MEM.set(alias,TypeStruct.UNUSED);
    // Re-flow all dependents
    Env.GVN.add_flow(PROGRESS);
    PROGRESS.clear();
  }
  private static TypeMem CACHE_DEF_MEM = TypeMem.ALLMEM;
  private static final Ary<Node> PROGRESS = new Ary<>(new Node[1],0);
  static TypeMem def_mem(Node n) {
    if( n!=null && PROGRESS.find(n)==-1 ) PROGRESS.push(n);
    return CACHE_DEF_MEM;
  }
  // Lift default memory to "nothing except external"
  public static void combo_def_mem() {
    CACHE_DEF_MEM = CACHE_DEF_MEM.set(1,TypeStruct.UNUSED);
  }


  @Override public Type live() {
    // Pre-combo, all memory is alive, except kills
    if( Combo.pre() ) return Env.KEEP_ALIVE._live;
    // During/post combo, everything that exits is live.
    deps_add(this);             // Which also means changes in value, change live
    return rmem().flatten_live_fields().slice_reaching_aliases(ralias());
  }

  @Override public Type live_use(Node def) {
    if( def==in(MEM_IDX) ) return _live;
    return Type.ALL;
  }

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
    CACHE_DEF_MEM = TypeMem.ALLMEM;
    PROGRESS.clear();
  }
}
