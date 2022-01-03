package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

import java.util.function.BiFunction;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

import static com.cliffc.aa.AA.unimpl;

// Function indices or function pointers; a single instance can include all
// possible aliased function pointers.  Function pointers can be executed, are
// not GC'd, and cannot be Loaded or Stored through (although they can be
// loaded & stored).
// 
// A function pointer includes a display (a back pointer to the enclosing
// environment); i.e. function pointers are "fat".  The display is typed as
// a TMP to a TypeStruct, or e.g. ANY (not live, nobody uses or cares) or XNIL.
//
// The TFP indicates if it carries a display or not; a TFP without a display
// cannot be called and has to be bound to a display first.  The TFP instead is
// bound to the prototype object for a type class, and requires a one-time
// binding to an actual object before being called.  For "static" functions,
// the prototype object is just the enclosing display and binds immediately.
//
// Other arguments are not currently curried in the TFP itself, only nargs.
//
// Each function index (or fidx) is a constant value, a classic code pointer.
// Cloning the code immediately also splits the fidx with a new fidx bit for
// both the original and the new code.
//
public final class TypeFunPtr extends Type<TypeFunPtr> implements Cyclic {
  // List of known functions in set, or 'flip' for choice-of-functions.
  // A single bit is a classic code pointer.
  public BitsFun _fidxs;        // Known function bits
  private int _nargs;           // Number of formals, including the ctrl, mem, display
  public Type _ret;             // Return scalar type
  private Type _dsp;            // Display; often a TMP to a TS; ANY is dead (not live, nobody uses).
  private boolean _has_dsp;     // Has a display bound
  boolean _cyclic; // Type is cyclic with a struct.  This is a summary property, not a part of the type, hence is not in the equals nor hash

  private TypeFunPtr init(BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    super.init("");
    _cyclic = false;
    _fidxs = fidxs; _nargs=nargs; _dsp=dsp; _ret=ret;
    return this;
  }
  @Override TypeFunPtr copy() { return _copy().init(_fidxs,_nargs,_dsp,_ret); }
  @Override public boolean cyclic() { return _cyclic; }
  @Override public void set_cyclic() { _cyclic = true; }
  @Override public void walk1( BiFunction<Type,String,Type> map ) { map.apply(_dsp,"dsp");  map.apply(_ret,"ret"); }
  @Override public void walk_update( UnaryOperator<Type> map ) { _dsp = map.apply(_dsp); _ret = map.apply(_ret); }

  public boolean has_dsp() { return _has_dsp; }
  public Type dsp() { assert _has_dsp; return _dsp; }
  void set_dsp(Type dsp) { assert un_interned() && _has_dsp; _dsp=dsp; }
  

  // Static properties hashcode, no edge hashes
  @Override int static_hash() {
    Util.add_hash(super.static_hash()+_nargs);
    Util.add_hash(_fidxs._hash);
    Util.add_hash(_dsp._type);
    return Util.get_hash();
  }
  // Excludes _ret._hash, which is part of cyclic hashes
  @Override int compute_hash() {
    assert _dsp._hash != 0;
    return Util.hash_spread(static_hash()+_dsp._hash);
  }

  // Static properties equals, no edges.  Already known to be the same class
  // and not-equals.
  @Override boolean static_eq(TypeFunPtr t) {
    return _fidxs == t._fidxs &&  _nargs == t._nargs && _dsp._type == t._dsp._type && _ret._type == t._ret._type;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    if( _fidxs!=tf._fidxs || _nargs != tf._nargs || _dsp!=tf._dsp ) return false;
    if( _ret==tf._ret ) return true;
    // Allow 2 closed 1-long return cycles to be equal.
    return _ret==this && tf._ret==tf;
  }
  // Structs can contain TFPs in fields and TFPs contain a Struct in a cycle.
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    if( _fidxs!=tf._fidxs || _nargs != tf._nargs ) return false;
    if( _dsp!=tf._dsp && !_dsp.cycle_equals(tf._dsp) ) return false;
    if( _ret!=tf._ret && (_ret==null || !_ret.cycle_equals(tf._ret)) ) return false;
    return true;
  }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    if( _fidxs==null ) return sb.p("[free]");
    _fidxs.str(sb);
    sb.p('{');                  // Collection (even of 1) start
    if( debug ) _dsp.str(sb,dups,mem,true).p(",");
    sb.p(_nargs).p(" ->");
    _ret.str(sb,dups,mem,debug).p(' ');
    return sb.p('}');
  }

  static { new Pool(TFUNPTR,new TypeFunPtr()); }

  // Lambda/FunPtr transfer functions wrap a TFP/FIDX around a return, possibly
  // repeatedly and must monotonically reach a fixed point.  Doing this by
  // restricting to a single in the return chain is not monotonic:
  //
  //  INPUT                   WRAP WITH [2]{->}               APPROX
  // ~scalar          ==>> [2]{-> ~scalar         } ==>> $[2  ]{->~scalar}
  // $[2  ]{->$[2  ]} ==>> [2]{-> $[2  ]{->$[2  ]}} ==>> $[2  ]{->$[2]   }
  // $[2,3]{->$[2,3]} ==>> [2]{-> $[2,3]{->$[2,3]}} ==>> $[2,3]{->$[2,3] } \___ NOT MONOTONIC
  // scalar           ==>> [2]{-> scalar          } ==>> $[2  ]{->scalar } /
  //
  // As the input falls from a $[2,3]{->$} cycle to scalar, the output (after
  // wrap-and-approximate) is not monotonic.

  // Make, without approximation, but test invariant holds
  public static TypeFunPtr make( BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    assert check(fidxs,ret);
    return malloc(fidxs,nargs,dsp,ret).hashcons_free();
  }

  // Invariant: FIDXS can appear in the length-1 cycle, but not in any prefix.
  private static boolean check(BitsFun fidxs, Type ret) {
    // Scan for a dup or the cycle
    while( ret instanceof TypeFunPtr) {
      TypeFunPtr tfp = (TypeFunPtr)ret;
      ret = tfp._ret;
      if( ret==tfp ) return true; // Found the ending cycle
      if( fidxs.overlaps(tfp._fidxs) ) return false; // Found a dup before the cycle
    }
    return true;
  }

  // Make and approximate an endlessly growing chain.
  static public TypeFunPtr makex( BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    return make(fidxs,nargs,dsp,makey(fidxs,ret));
  }
  // Dunno if another fidx up ahead or not
  static private Type makey( BitsFun fidxs, Type ret ) {
    if( !(ret instanceof TypeFunPtr) )
      return ret;               // End of chain, correct as-is
    TypeFunPtr tfp = (TypeFunPtr)ret;
    // Overlaps; this becomes the new cycle.
    if( fidxs.overlaps(tfp._fidxs) ) {
      TypeFunPtr cyc = tfp.malloc_from();
      cyc.gather_cycle(tfp);
      cyc._ret=cyc;
      return cyc.tfp_install();
    }
    if( tfp._ret==tfp ) return ret;
    Type rez = makey(fidxs,tfp._ret);
    return rez==tfp._ret ? ret : tfp.make_from(tfp._dsp,rez);
  }

  // Gather all the fidxs from here to the end of the ret-chain
  private void gather_cycle(Type x) {
    if( !(x instanceof TypeFunPtr) ) return;
    TypeFunPtr tfp = (TypeFunPtr)x;
    _fidxs = _fidxs.meet(tfp._fidxs);
    _nargs = Math.min(_nargs,tfp._nargs);
    _dsp   = _dsp.meet(tfp._dsp);
    if( tfp._ret!=tfp )
      gather_cycle(tfp._ret);
  }

  // Install a cyclic $:TFP->...-> $
  private TypeFunPtr tfp_install() {
    TypeFunPtr old = (TypeFunPtr)intern_lookup();
    if( old!=null ) {           // Return prior hit
      for( TypeFunPtr tfp = (TypeFunPtr)_ret; tfp!=this; tfp = (TypeFunPtr)tfp._ret )
        POOLS[TFUNPTR].free(tfp,null);
      return POOLS[TFUNPTR].free(this,old);
    }
    // RDUAL is recursive, one call does the cycle
    rdual();
    for( TypeFunPtr tfp = (TypeFunPtr)_ret; tfp!=this; tfp = (TypeFunPtr)tfp._ret )
      tfp.retern();
    retern();
    return this;
  }


  // Allocate and init
  private static TypeFunPtr malloc(BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(fidxs,nargs,dsp,ret);
  }
  private TypeFunPtr malloc_from() {
    var tfp = malloc(_fidxs,_nargs,_dsp,null);
    tfp._hash = _hash;
    return tfp;
  }

  public static TypeFunPtr make( int fidx, int nargs, Type dsp, Type ret ) { return make(BitsFun.make0(fidx),nargs,dsp,ret); }
  public static TypeFunPtr make_new_fidx( int parent, int nargs, Type dsp, Type ret ) { return make(BitsFun.make_new_fidx(parent),nargs,dsp,ret); }
  public static TypeFunPtr make( BitsFun fidxs, int nargs) { return make(fidxs,nargs,TypeMemPtr.NO_DISP,Type.SCALAR); }
  public        TypeFunPtr make_from( TypeMemPtr dsp ) { return make(_fidxs,_nargs, dsp,_ret); }
  public        TypeFunPtr make_from( BitsFun fidxs  ) { return fidxs==_fidxs ? this : make( fidxs,_nargs,_dsp,_ret); }
  public        TypeFunPtr make_from( Type dsp, Type ret ) { return dsp==_dsp && ret==_ret ? this : make(_fidxs,_nargs, dsp,ret); }
  public        TypeFunPtr make_no_disp( ) { return make(_fidxs,_nargs,TypeMemPtr.NO_DISP,_ret); }
  public static TypeFunPtr make_sig(TypeStruct formals,Type ret) { throw unimpl(); }
  public static TypeMemPtr DISP = TypeMemPtr.DISPLAY_PTR; // Open display, allows more fields

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.FULL ,1,Type.ALL,Type.ALL);
  public  static final TypeFunPtr ARG2   =         make(BitsFun.FULL ,2,Type.ALL,Type.ALL);
  public  static final TypeFunPtr EMPTY  =         make(BitsFun.EMPTY,0,Type.ANY,Type.ANY);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,ARG2/*,EMPTY.dual()*/};

  @Override protected TypeFunPtr xdual() {
    return malloc(_fidxs.dual(),-_nargs,_dsp.dual(),_ret.dual());
  }
  @Override protected TypeFunPtr rdual() {
    assert _hash==compute_hash();
    if( _dual != null ) return _dual;
    TypeFunPtr dual = _dual = malloc(_fidxs.dual(),-_nargs,null,null);
    dual._dual = this;          // Stop the recursion
    dual._dsp = _dsp.rdual();
    dual._hash = dual.compute_hash();
    dual._ret = _ret.rdual();
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TFUNPTR:break;
    case TFLT:
    case TINT:
    case TMEMPTR:
    case TRPC:   return cross_nil(t);
    case TSTRUCT:
    case TTUPLE:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeFunPtr tf = (TypeFunPtr)t;
    BitsFun fidxs = _fidxs.meet(tf._fidxs);
    // If both are short cycles, the result is a short cycle
    if( _ret==this && tf._ret==tf )  return makey(fidxs,tf);

    // TODO: renable this
    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    //TypeFunPtr min_nargs = _nargs < tf._nargs ? this : tf;
    //TypeFunPtr max_nargs = _nargs < tf._nargs ? tf : this;
    //int nargs = min_nargs.above_center() ? max_nargs._nargs : min_nargs._nargs;
    //int nargs = fidxs.above_center() ? Math.max(_nargs,tf._nargs) : Math.min(_nargs,tf._nargs);
    int nargs = (_nargs ^ tf._nargs) > 0 ? Math.min(_nargs,tf._nargs) : Math.max(_nargs,tf._nargs);
    Type dsp = _dsp.meet(tf._dsp);
    // Otherwise, recursively find the return
    Type ret = _ret.meet(tf._ret);
    return makex(fidxs,nargs,dsp,ret);
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit
  public int nargs() { return Math.abs(_nargs); }

  // Widens, not lowers.
  @Override public TypeFunPtr simple_ptr() {
    Type ds = _dsp.simple_ptr();
    Type rs = _ret.simple_ptr();
    if( _dsp==ds && _ret==rs ) return this;
    return make_from(ds,rs);
  }

  @Override public boolean above_center() {
    return _fidxs.above_center() || _fidxs.is_empty();
  }
  @Override public boolean may_be_con()   {
    return _dsp.may_be_con() &&
      _fidxs.abit() != -1;
  }
  @Override public boolean is_con()       {
    return _dsp==TypeMemPtr.NO_DISP && // No display (could be constant display?)
      // Single bit covers all functions (no new children added, but new splits
      // can appear).  Currently, not tracking this at the top-level, so instead
      // just triggering off of a simple heuristic: a single bit above BitsFun.FULL.
      _fidxs.abit() > 1 ;
  }
  @Override public boolean must_nil() { return _fidxs.test(0) && !_fidxs.above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make_from(bits);
  }
  @Override public Type meet_nil(Type nil) {
    assert nil==NIL || nil==XNIL;
    // See testLattice15.
    if( nil==XNIL )
      return _fidxs.test(0) ? (_fidxs.above_center() ? XNIL : SCALAR) : NSCALR;
    if( _fidxs.above_center() ) return make_from(BitsFun.NIL);
    BitsFun fidxs = _fidxs.above_center() ? _fidxs.dual() : _fidxs;
    return make_from(fidxs.set(0));
  }
  // Used during approximations, with a not-interned 'this'.
  // Updates-in-place.
  public Type ax_meet_nil(Type nil) {
    throw com.cliffc.aa.AA.unimpl();
  }

  //// Lattice of conversions:
  //// -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  ////    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  ////  0 requires no/free conversion (Int8->Int64, F32->F64)
  //// +1 requires a bit-changing conversion (Int->Flt)
  //// 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  //@Override public byte isBitShape(Type t) {
  //  if( t._type == TNIL ) return 0;                  // Dead arg is free
  //  if( t._type == TSCALAR ) return 0;               // Scalar is OK
  //  return (byte)(t instanceof TypeFunPtr ? 0 : 99); // Mixing TFP and a non-ptr
  //}
  @SuppressWarnings("unchecked")
  @Override public void walk( Predicate<Type> p ) { if( p.test(this) ) { _dsp.walk(p); _ret.walk(p); } }

  // Generic functions
  TypeFunPtr _sharpen_clone(TypeMemPtr dsp) {
    TypeFunPtr tf = copy();
    tf._dsp = dsp;
    return tf;
  }
  @Override TypeFunPtr _widen() { return GENERIC_FUNPTR; }

  @Override public Type make_from(Type head, TypeMem map, VBitSet visit) {
    throw unimpl();
  }

  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) {
    //return _dsp.repeats_in_cycles(head,bs);
    throw unimpl();
  }

  // All reaching fidxs, including any function returns
  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    if( Type.ARF.tset(_uid) ) return _fidxs;
    // Myself, plus any function returns
    return _fidxs.meet(_ret._all_reaching_fidxs(tmem));
  }

}
