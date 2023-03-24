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
  // [program exit control, program exit memory, program exit value, escaping RetNodes and global CallNodes... ]
  public RootNode() { super(OP_ROOT, null, null, null); }

  @Override boolean is_CFG() { return true; }
  @Override public boolean is_mem() { return true; }

  TypeMem rmem() {
    return _val instanceof TypeTuple tt ? (TypeMem)tt.at(MEM_IDX) : TypeMem.ALLMEM.oob(_val.above_center());
  }
  Type rrez() {
    return _val instanceof TypeTuple tt ? tt.at(REZ_IDX) : _val.oob(TypeNil.SCALAR);
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
  
  // Used by TV3 as_flow for a external Leaf value.
  public TypeNil ext_scalar(Node dep) {
    assert Combo.HM_FREEZE;
    return (TypeNil)(_val instanceof TypeTuple tt
                     ? tt.at(3)
                     : _val.oob(TypeNil.INTERNAL));
  }
  // Used by CallEpiNode for the return type of unknown external functions
  public TypeNil ext_caller() {
    return (TypeNil)(_val instanceof TypeTuple tt
                     ? tt.at(3)
                     : _val.oob(TypeNil.SCALAR));
  }
  
  // Output value is:
  // [Ctrl, All_Mem_Minus_Dead, Rezult, global_escaped_[fidxs, aliases]]
  @Override public TypeTuple value() {
    // Conservative final result.  Until Combo external calls can still wire, and escape arguments
    Node rez = in(REZ_IDX);
    if( rez==null || Combo.pre() )
      return TypeTuple.make(Type.CTRL,def_mem(this),TypeRPC.ALL_CALL,TypeNil.SCALAR);
    Type trez = rez._val;
    // Conservative final memory
    Node mem = in(MEM_IDX);
    TypeMem tmem = mem._val instanceof TypeMem tmem0 ? tmem0 : mem._val.oob(TypeMem.ALLMEM);
    // All external aliases already escaped
    tmem = tmem.set(BitsAlias.EXTX,TypeStruct.ISUSED);
    tmem = tmem.set(BitsAlias.STRX,TypeMemPtr.STRPTR._obj);
    
    // Reset for walking
    // Walk, finding escaped aliases and fidxs
    escapes_reset(tmem);
    escapes(trez);
    // Walk the global Calls and Rets also
    for( int i=ARG_IDX; i<len(); i++ ) {
      if( in(i) instanceof CallNode call ) {
        if( call.tfp()._fidxs.test(BitsFun.EXTX) )
          for( int j=DSP_IDX; j<call.nargs(); j++ ) {
            call.in(j).deps_add(this);
            escapes(call.val(j));
          }
      } else {
        escapes(((RetNode)in(i)).rez()._val);
      }
    }

    // Roots value is all reachable alias memory shapes, plus all reachable
    // (escaped) aliases and functions.
    return TypeTuple.make(Type.CTRL,
                          EXT_MEM,
                          trez,
                          escapes_get());
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
  private static BitsAlias EXT_ALIASES;
  private static BitsFun   EXT_FIDXS  ;
          static TypeMem   EXT_MEM    ;

  // Called before computing to reset state
  private static void escapes_reset(TypeMem tmem) {
    VISIT.clear();
    ALIASES.clear();
    EXT_ALIASES = BitsAlias.EMPTY;
    EXT_FIDXS   = BitsFun  .EMPTY;
    EXT_MEM = tmem;
    // Kill the killed
    for( int alias : KILL_ALIASES )
      EXT_MEM = EXT_MEM.set(alias,TypeStruct.UNUSED);
  }
  // Called after computing to get state
  private static TypeNil escapes_get() {
    return TypeNil.make(false,false,false,
                        EXT_ALIASES.meet(BitsAlias.EXT),
                        EXT_FIDXS  .meet(BitsFun  .EXT));
  }

  // Called once per escaping value
  private static void escapes( Type t ) {
    _escapes(t);
    while( !ALIASES.isEmpty() )
      _escapes(EXT_MEM.at(ALIASES.pop()));
  }
  private static void _escapes( Type t ) {
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
            ret.deps_add(Env.ROOT);
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
    BitsFun fidxs = BitsFun.EXT;
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
    Env.ROOT.add_flow();
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
    // During/post combo, check external Call users
    Type live = Type.ANY;           // Start at lattice top
    for( Node use : _uses )         // Computed across all uses
      if( use._live != Type.ANY && use.is_mem() ) { // If use is alive, propagate liveness
        Type ulive = use.live_use(this);
        live = live.meet(ulive); // Make alive used fields
      }
    if( live==Type.ANY ) return live;
    TypeMem mem = (TypeMem)live;
    // Liveness for return value
    TypeMem mem2 = rmem().slice_reaching_aliases(ralias()).flatten_live_fields();
    return mem.meet(mem2.meet(TypeMem.EXTMEM));
  }

  @Override public Type live_use(Node def) {
    if( def==in(CTL_IDX) ) return Type.ALL;
    if( def==in(MEM_IDX) ) return _live;
    if( def==in(REZ_IDX) ) return Type.ALL;
    assert def instanceof CallNode || def instanceof RetNode;
    return _live;               // Global calls take same memory as me
  }

  // All escaping FIDXS are wired.  If Escapes is NALL, these edges are virtual.
  boolean is_CG(boolean precise) {
    BitsFun fidxs = rfidxs();
    int non_prim_rets=0;
    // All currently wired Calls and Rets are sensible
    for( int i=ARG_IDX; i<len(); i++ ) {
      if( in(i) instanceof RetNode ret ) {
        if( !ret.is_prim() ) non_prim_rets++;
        FunNode fun = ret.fun();
        if( fun._defs.last() != this ) return false;
        if( !rfidxs().test_recur(ret._fidx) ) return false;
      } else {
        CallNode call = (CallNode)in(i);
        if( call.cepi()._defs.last()!=this ) return false;
      }
    }
    if( fidxs.above_center() || fidxs==BitsFun.NALL )
      return non_prim_rets==0; // If escapes is ALL, then all ret edges are virtual
    // All fidxs are wired if precise.  Imprecise allows some new fidxs not yet wired.
    if( precise )
      for( int fidx : fidxs )
        if( fidx != BitsAlias.EXTX && // External fidxs cannot be wired
            _defs.find(RetNode.get(fidx)) < ARG_IDX )
          return false;         // Has unwired fidx
    return true;
  }

  public boolean CG_wire() {
    assert is_CG(false);
    boolean progress=false;

    // Wire escaping fidxs: Root -> Ret... Fun -> Root
    BitsFun fidxs = rfidxs();
    if( fidxs!=BitsFun.NALL ) {
      for( int fidx : fidxs ) {
        if( fidx == BitsAlias.EXTX ) continue; // No wiring external functions
        RetNode ret = RetNode.get(fidx);
        if( _defs.find(ret) >= ARG_IDX ) continue; // Already wired
        // Wire escaping
        ret.fun().add_def(this).add_flow();
        add_def(ret);
        progress = true;
      }
    }
    assert is_CG(true);
    return progress;
  }
  
  @Override public Node ideal_reduce() {
    if( in(0)==null ) return null;
    Node cc = fold_ccopy();
    if( cc!=null ) return cc;
    // See if the result can ever refer to local memory.
    Node rez = in(REZ_IDX);
    if( in(MEM_IDX) != Env.XMEM &&
        cannot_lift_to(rez._val,TypeMemPtr.ISUSED) &&
        cannot_lift_to(rez._val,TypeFunPtr.GENERIC_FUNPTR) ) {
      set_def(MEM_IDX,Env.XMEM);
      Env.XMEM.xliv();          // Added a new use
      return this;
    }
    if( CG_wire() ) return this;
    
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
    while( len() > REZ_IDX+1 ) {
      Node n = _defs.last();
      if( n instanceof CallNode call ) {
        call.cepi().unwire(call,this,this);
      } else if( n instanceof RetNode ret ) {
        ret.fun().pop();
        pop();
      }
      else throw unimpl();
    }
    EXT_FUNS_BY_NARGS.clear();
    KILL_ALIASES = BitsAlias.EMPTY;
    CACHE_DEF_MEM = TypeMem.ALLMEM;
    PROGRESS.clear();
  }
}
