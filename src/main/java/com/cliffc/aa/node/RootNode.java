package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
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

  // Used by TV3 as_flow for an external Leaf value.
  public TypeNil ext_scalar(Node dep) {
    assert Combo.HM_FREEZE;
    return (TypeNil)(_val instanceof TypeTuple tt
                     ? tt.at(3)
                     : _val.oob(TypeNil.EXTERNAL));
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
    // Kill the killed
    for( int alias : KILL_ALIASES )
      tmem = tmem.set(alias,TypeStruct.UNUSED);
    // All primitive aliases have sharper types
    tmem = PrimNode.primitive_memory(this,tmem);

    // Reset for walking
    escapes_reset(tmem);
    // Walk, finding escaped aliases and fidxs
    escapes(rez);
    // Walk the global Calls and Rets also
    for( int i=ARG_IDX; i<len(); i++ ) {
      if( in(i) instanceof CallNode call ) {
        // If Call is calling an externally defined function then all args escape
        if( call.tfp()._fidxs.overlaps(BitsFun.EXT) ) {
          for( int j=DSP_IDX; j<call.nargs(); j++ )
            escapes( call.arg(j) );
        }
      } else
        // If function may be reached from Root, the return escapes.
        escape_ret((RetNode)in(i));
    }

    // Roots value is all reachable alias memory shapes, plus all reachable
    // (escaped) aliases and functions.
    TypeMem ext_mem = EXT_MEM;
    TypeNil escapes = escapes_get();
    for( int alias : KILL_ALIASES ) assert ext_mem.at(alias)==TypeStruct.UNUSED;
    return TypeTuple.make(Type.CTRL,
                          ext_mem,
                          trez,
                          escapes);
  }

  // Escape all Root results.  Escaping functions are called with the most
  // conservative HM-compatible arguments.  Escaping functions update the
  // global memory state, and their return has to be visited also.

  // Escaping pointers escape their structs, including their fields.  Escaping
  // Structs state is pulled from the global memory state.  Struct fields can
  // include new escaping functions, which bring in new memory state.

  // This cycle fcn->mem->ptr->struct->fcn requires a worklist algo.

  private static final VBitSet EVISIT = new VBitSet();
  // Results computed here, and modified at each call.
  private static BitsAlias EXT_ALIASES;
  private static BitsFun   EXT_FIDXS  ;
          static TypeMem   EXT_MEM    ;

  // Called before computing to reset state
  private static void escapes_reset(TypeMem tmem) {
    EVISIT.clear();
    EXT_MEM = tmem;             // Memory escaping, plus escaped primitives
    EXT_ALIASES = BitsAlias.EXT;
    EXT_FIDXS   = BitsFun  .EXT;
  }
  // Called after computing to get state
  private static TypeNil escapes_get() {
    TypeNil tn = TypeNil.make(false,false,false, EXT_ALIASES, EXT_FIDXS );
    EVISIT.clear();
    return tn;
  }

  // Called once per escaping value
  private void escapes( Node n ) {
    n.deps_add(this);
    _escapes(n._val);
  }
  private static void _escapes( Type t ) {
    if( EVISIT.tset(t._uid) ) return;
    switch( t ) {
      case TypeStruct ts -> {
        assert ts._fidxs == BitsFun.EMPTY && ts._aliases == BitsAlias.EMPTY;
        if( ts._def != Type.ALL )
          _escapes(ts._def); // TODO: BIG CHEAT, NEED external memory to use e.g. Root escapes
        for( TypeFld fld : ts )
          // Root widens all non-final fields
          _escapes(fld._access == TypeFld.Access.Final ? fld._t : TypeNil.SCALAR);
      }
      case TypeNil tn -> {
        if( tn == TypeNil.XNIL) return;
        if( !tn._aliases.above_center()) {
          // Add to the set of escaped aliases
          for( int alias : tn._aliases) {
            if( KILL_ALIASES.test_recur(alias)) continue; // Already dead
            if(  EXT_ALIASES.test_recur(alias)) continue; // Never seen before escape
            EXT_ALIASES = EXT_ALIASES.set(alias);
            // TODO: walk the memory for this escaped alias?
            //NewNode nnn = NewNode.get(alias);
            //if( nnn != null )
            //  throw unimpl();
          }
        }
        if( !tn._fidxs.above_center()) {
          // Walk all escaped function args, and call them (like an external
          // Apply might) with the most conservative flow arguments possible.
          for( int fidx : tn._fidxs) {
            if( EXT_FIDXS.test_recur(fidx)) continue; // Never seen before escape
            RetNode ret = RetNode.get(fidx);
            if( ret != null ) {
              FunPtrNode fptr = ret.funptr();
              if( fptr != null ) {
                EXT_FIDXS = EXT_FIDXS.set(fidx);
                fptr.tvar().widen((byte)1,false); // HMT widen
                fptr.deps_add(Env.ROOT); // Un-escaping by deleting FunPtr will trigger Root recompute
                escape_ret(ret);
              }
            }
          }
          // The return (but not inputs, so not display) also escapes
          if( tn instanceof TypeFunPtr tfp)
            _escapes(tfp._ret);
        }
      }
      case TypeTuple tup -> {
        assert tup.len()== AA.ARG_IDX;
        TypeMem mem = (TypeMem)tup.at(MEM_IDX);
        TypeMem mem2 = mem.remove(KILL_ALIASES);
        EXT_MEM = (TypeMem)EXT_MEM.meet(mem2);
        _escapes(tup.at(REZ_IDX));
      }
      case TypeMem mem -> {
        TypeStruct[] tss = mem.alias2objs();
        for( int i = 1; i < tss.length; i++ )
          if( tss[i] != null ) {
            _escapes(tss[i]);
            if( BitsAlias.INT.test_recur(i) && EXT_MEM.at(i)!=tss[i] && !KILL_ALIASES.test(i) )
              EXT_MEM = EXT_MEM.set(i,(TypeStruct)EXT_MEM.at(i).meet(tss[i]));
          }
      }
      default -> {
        //if( t == Type.ALL ) throw unimpl(); // Typical error case
        assert t.getClass() == Type.class;
      }
    }
  }
  static void escape_ret(RetNode ret) {
    // If function is reachable from Root, then the return escapes
    FunNode fun = ret.fun();
    if( fun._defs.last() instanceof RootNode || fun.unknown_callers(null) )
      _escapes(ret._val);
  }

  // Given a TV3, mimic a matching flow Type from all possible internal
  // escaping aliases.  Escaped functions might be called with these aliases.
  public BitsAlias matching_escaped_aliases(TV3 tv3, Node dep) {
    // Caller result depends on escaping fidxs
    if( dep!=null ) deps_add(dep);
    BitsAlias ralias = ralias();
    if( ralias==BitsAlias.NALL ) return BitsAlias.NALL;
    BitsAlias aliases = BitsAlias.EMPTY;
    for( int alias : ralias )
      if( alias>BitsAlias.EXTX && !BitsAlias.EXT.test_recur(alias) &&
          tv3.exact_unify_ok(NewNode.get(alias).tvar()) )
        aliases = aliases.set(alias); // Compatible escaping alias
    return aliases;
  }

  // Given a TV3 lam, mimic a matching flow TypeFunPtr from all possible
  // internal but escaping fidxs.  Escaped functions might be called from Root.
  public BitsFun matching_escaped_fidxs(TVLambda lam, Node dep) {
    // Caller result depends on escaping fidxs
    if( dep!=null ) deps_add(dep);
    BitsFun fidxs = BitsFun.EXT;
    for( int fidx : rfidxs() ) {
      RetNode ret = RetNode.get(fidx);
      if( ret != null ) {     // External function, no real sig or def
        TV3 funtvar = ret.funptr().tvar();
        if( funtvar instanceof TVLambda esc_lam && lam.exact_unify_ok(esc_lam) )
          fidxs = fidxs.set(fidx); // Compatible escaping fidx
      }
    }
    return fidxs;
  }

  // Default memory during initial Iter, before Combo: all memory minus the
  // kills.  Many things produce def_mem, and in general it has to be used
  // until Combo finishes the Call Graph.
  static BitsAlias KILL_ALIASES = BitsAlias.EMPTY;
  static void kill_alias( int alias ) {
    if( KILL_ALIASES.test_recur(alias) ) return;
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
    for( int kill : KILL_ALIASES )
      mem = mem.set(kill,TypeStruct.UNUSED);
    // Liveness for return value: All reaching aliases plus their escapes are alive.
    BitsAlias ralias = ralias();
    if( ralias==BitsAlias.EMPTY ) return mem;
    if( ralias.above_center() ) return mem;
    if( ralias.test(BitsAlias.ALLX) ) return TypeMem.ALLMEM;
    TypeMem rlive = TypeMem.make(ralias,TypeStruct.ISUSED);
    return mem.meet(rlive);
  }

  @Override public Type live_use(Node def) {
    if( def==in(CTL_IDX) ) return Type.ALL;
    if( def==in(MEM_IDX) ) return _live;
    if( def==in(REZ_IDX) ) {
      // Sharpen liveness for escaping function displays
      if( val(REZ_IDX) instanceof TypeFunPtr tfp ) {
        if( tfp.dsp() instanceof TypeMemPtr tmp ) {
          if( !ralias().overlaps(tmp.aliases()) )
            return CallNode.FP_LIVE;
        } else if( tfp.dsp()==Type.ANY )
          return CallNode.FP_LIVE;
      }
      if( val(REZ_IDX)==Type.ANY ) return Type.ANY; // TODO: Surely broken
      return Type.ALL;
    }
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
        if( fidx != BitsFun.EXTX && // External fidxs cannot be wired
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
        if( fidx == BitsFun.EXTX ) continue; // No wiring external functions
        RetNode ret = RetNode.get(fidx);
        if( _defs.find(ret) >= ARG_IDX ) continue; // Already wired
        // Wire escaping
        ret.fun().add_def(this).add_flow();
        add_def(ret);
        add_flow(); // Recompute root values to include function return memory
        ret.add_flow();
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

    // See if we can unescape some functions
    for( int i=ARG_IDX; i<len(); i++ )
      if( in(i) instanceof RetNode ret && ret.funptr()==null ) {
        del(i--);
        if( ret._uses._len==0 ) ret.kill();
      }
    
    // Turned off, since int/flt constant returns actually have a TVClz with a
    // TVPtr in memory which is used for the HM return.
    
    //// See if the result can ever refer to local memory.
    //Node rez = in(REZ_IDX);
    //if( in(MEM_IDX) != Env.XMEM &&
    //    cannot_lift_to(rez._val,TypeMemPtr.ISUSED) &&
    //    cannot_lift_to(rez._val,TypeFunPtr.GENERIC_FUNPTR) ) {
    //  set_def(MEM_IDX,Env.XMEM);
    //  Env.XMEM.xliv();          // Added a new use
    //  return this;
    //}
    
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

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    TV3 tv3 = in(REZ_IDX).set_tvar().find();
    tv3.widen((byte)1,false);   // Widen result, since escaping
    return tv3;
  }

  @Override public boolean unify( boolean test ) { return false; }
  
  // Unify trailing result ProjNode with RootNode results; but no unification
  // with anything from Root, all results are independent.
  @Override public boolean unify_proj( ProjNode proj, boolean test ) { return false; }

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
    KILL_ALIASES = BitsAlias.EMPTY;
    CACHE_DEF_MEM = TypeMem.ALLMEM;
    PROGRESS.clear();
  }
}
