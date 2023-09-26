package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.AryInt;

import java.util.function.Predicate;

import static com.cliffc.aa.AA.*;


// Program execution start

// RootNode inputs are:
// [program exit control,
//  program exit memory,
//  program exit value,
//  primitive memory
//    TODO: primitive NewNode aliases, eg PrimNode.PINT
// Any number in any order:
//  escaping RetNodes - functions callable from Universe
//  global CallNodes - Calls to unknown functions from Universe
// ]

public class RootNode extends Node {
  public RootNode(Node... defs) { super(OP_ROOT, defs); }

  @Override boolean is_CFG() { return true; }
  @Override public boolean is_mem() { return true; }

  TypeMem rmem(Node dep) {
    deps_add(dep);
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
    //assert Combo.HM_FREEZE;
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
    //TypeMem tmem = mem._val instanceof TypeMem tmem0 ? tmem0 : mem._val.oob(TypeMem.ALLMEM);
    //// Primitive memory
    ////tmem = PrimNode.primitive_memory(this,tmem);
    //tmem = (TypeMem)tmem.meet(val(ARG_IDX));
    TypeMem tmem = (TypeMem)val(ARG_IDX);
    // Conservative final result.  Until Combo external calls can still wire, and escape arguments
    if( Combo.pre() )
      return TypeTuple.make(Type.CTRL,tmem.make_from(BitsAlias.EXTX,TypeStruct.ISUSED),TypeNil.SCALAR,TypeNil.SCALAR);
    

    // Walk the 'rez', all Call args (since they call Root, their args escape)
    // and function rets (since called from Root, their return escapes).
    AryInt awork = new AryInt();
    AryInt fwork = new AryInt();
    TypeNil escs = TypeNil.EXTERNAL;
    Type trez = val(REZ_IDX);   // Returned value is the starting point
    escs = _add_all(escs,awork,fwork,trez);
    for( int i=ARG_IDX+1; i<len(); i++ ) {
      if( escs==TypeNil.SCALAR ) break; // Already maxed out
      if( in(i) instanceof CallNode call ) {
        // If Call is calling an externally defined function then all args escape
        if( call.tfp()._fidxs.overlaps(BitsFun.EXT) ) {
          for( int j=DSP_IDX; j<call.nargs(); j++ ) {
            call.arg(j).deps_add(this);
            escs = _add_all(escs,awork,fwork,call.arg(j)._val);
          }
        }
      } else {
        // If function may be reached from Root, the return escapes.
        assert in(i) instanceof RetNode;
        in(i).deps_add(this);
        Type t = in(i)._val;
        escs = _add_all(escs,awork,fwork,t);
        if( t instanceof TypeTuple tt ) { // ANY is OK
          tmem = (TypeMem)tmem.meet(tt.at(MEM_IDX));
        } else assert t.above_center();
      }
    }
    // Kill the killed
    for( int alias : KILL_ALIASES )
      tmem = tmem.set(alias,TypeStruct.UNUSED);

    // Keep a visit bit for aliases & fidxs.  No need to visit twice.  If a bit
    // alias/fidx is set in the answer, then it must be on the to-do list.
    // Visited aliases use the TMEM memory struct, and recursively visit.
    while( awork.len()!=0 || fwork.len()!= 0 ) {
      if( awork._len>0 ) {
        TypeStruct ts = tmem.at(awork.pop());
        for( TypeFld tfld : ts ) {
          Type fld = tfld._t;
          escs = _add_all(escs,awork,fwork,fld);
        }
      }
      if( fwork._len>0 ) {
        RetNode ret = RetNode.get(fwork.pop());
        if( ret != null ) { // Can be null in error situations
          FunPtrNode fptr = ret.funptr();
          if( fptr != null ) {
            // fptr.tvar().widen((byte)1,false); // HMT widen
            fptr.deps_add(this); // Un-escaping by deleting FunPtr will trigger Root recompute
            escs = _add_all(escs,awork,fwork,ret._val);
          } else throw unimpl(); // Untested, can i get a null here post-combo?
        }
      }
    }

    // Kill the killed
    escs = TypeNil.make(false,false,false,escs._aliases.subtract(KILL_ALIASES),escs._fidxs);

    TypeStruct extstr = tmem.at(BitsAlias.EXTX);
    TypeStruct extstr2 = (TypeStruct)extstr.meet( TypeStruct.make(false,escs,TypeFlds.EMPTY) );
    tmem = tmem.set(BitsAlias.EXTX,extstr2);

    // RootNode value is a 4-pack
    return TypeTuple.make(Type.CTRL, tmem, trez, escs);
  }

  private TypeNil _add_all( TypeNil escs, AryInt awork, AryInt fwork, Type t ) {
    return switch( t ) {
    case TypeNil tn -> {
      if( tn==TypeNil.XNIL ) yield escs;
      boolean progress = _add_one( escs._aliases, awork, tn._aliases )
        |                _add_one( escs._fidxs  , fwork, tn._fidxs   );
      yield progress ? (TypeNil)escs.meet( tn ) : escs;
    }
    case TypeTuple tt -> _add_all( escs, awork, fwork, tt.at( 2 ) );
    default -> t.above_center() ? escs : TypeNil.SCALAR;
    };
  }

  private <B extends Bits<B>> boolean _add_one( Bits escs, AryInt work, Bits xn ) {
    if( xn.isa(escs) ) return false;
    Bits<B> bs = xn.subtract(escs);
    for( int b : bs ) work.push(b);
    return true;
  }


  // Given a TV3, mimic a matching flow Type from all possible internal
  // escaping aliases.  Escaped functions might be called with these aliases.
  public BitsAlias matching_escaped_aliases(TV3 tv3, Node dep) {
    // Caller result depends on escaping fidxs
    if( dep!=null ) deps_add(dep);
    BitsAlias ralias = ralias();
    if( ralias==BitsAlias.NALL ) return BitsAlias.NALL;
    BitsAlias aliases = BitsAlias.EXT;
    for( int alias : ralias )
      for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) ) {
        NewNode nnn = NewNode.get(kid);
        if( nnn!=null && tv3.exact_unify_ok(nnn.tvar()) )
          aliases = aliases.set(kid); // Compatible escaping alias
      }
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
  public static TypeMem def_mem(Node n) {
    if( n!=null && PROGRESS.find(n)==-1 ) PROGRESS.push(n);
    return CACHE_DEF_MEM;
  }
  // Lift default memory to "nothing except external"
  public static void combo_def_mem() {
    CACHE_DEF_MEM = CACHE_DEF_MEM.set(1,TypeStruct.UNUSED);
  }


  @Override public Type live() {
    // Pre-combo, all memory is alive, except kills
    // During/post combo, check external Call users
    Type live = Combo.pre() ? TypeMem.ALLMEM : super.live(false);
    if( live==Type.ANY ) return live;
    TypeMem mem = (TypeMem)live;
    // Kill the killables
    for( int kill : KILL_ALIASES )
      mem = mem.set(kill,TypeStruct.UNUSED);
    if( Combo.pre() ) return mem;
    // Liveness for return value: All reaching aliases plus their escapes are alive.
    BitsAlias ralias = ralias();
    if( ralias==BitsAlias.EMPTY ) return mem;
    if( ralias.above_center() ) return mem;
    if( ralias.test(BitsAlias.ALLX) ) return TypeMem.ALLMEM;
    TypeMem rlive = TypeMem.make(ralias,TypeStruct.ISUSED);
    return mem.meet(rlive);
  }

  @Override public Type live_use( int i ) {
    if( i==CTL_IDX ) return Type.ALL;
    if( i==MEM_IDX ) return _live;
    if( i==REZ_IDX ) {
      // Sharpen liveness for escaping function displays
      if( val(REZ_IDX) instanceof TypeFunPtr tfp ) {
        if( tfp.dsp().above_center() )
          return CallNode.FP_LIVE;
        if( tfp.dsp() instanceof TypeMemPtr tmp &&
            !ralias().overlaps(tmp.aliases()) )
          return CallNode.FP_LIVE;
      }
      deps_add(in(REZ_IDX));
      if( val(REZ_IDX)==Type.ANY ) return Type.ANY; // TODO: Surely broken
      return Type.ALL;
    }
    assert in(i) instanceof CallNode || in(i) instanceof RetNode;
    return _live;               // Global calls take same memory as me
  }

  // All escaping FIDXS are wired.  If Escapes is NALL, these edges are virtual.
  boolean is_CG(boolean precise) {
    BitsFun fidxs = rfidxs();
    int non_prim_rets=0;
    // All currently wired Calls and Rets are sensible
    for( int i=ARG_IDX+1; i<len(); i++ ) {
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
    // During pre-Combo and lifting, if escapes is NALL then all edges are
    // virtual.  During & after Combo, if escapes is NALL then Root has fallen
    // hard (generally an error condition), and we might have physical edges
    // which can lazily be made virtual.
    if( fidxs.above_center() || fidxs==BitsFun.NALL )
      return non_prim_rets==0 || !Combo.pre();
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
    if( fidxs!=BitsFun.NALL && !fidxs.above_center() ) {
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
  public static void reset_to_init0() {
    KILL_ALIASES = BitsAlias.EMPTY;
    CACHE_DEF_MEM = TypeMem.ALLMEM;
    PROGRESS.clear();
  }
}
