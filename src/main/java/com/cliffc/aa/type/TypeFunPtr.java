package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.*;

import java.util.function.*;

import static com.cliffc.aa.AA.unimpl;


// Function indices or function pointers; a single instance can include all
// possible aliased function pointers.  Function pointers can be executed, are
// not GC'd, and cannot be Loaded or Stored through (although they can be
// loaded & stored).
//
// A TypeFunPtr includes a set of function indices and the display and NOT
// e.g. the function arguments nor formals.  Formals are stored in the FunNode.
//
// Each function index (or fidx) is a constant value, a classic code pointer.
// Cloning the code immediately also splits the fidx with a new fidx bit for
// both the original and the new code.
//
public final class TypeFunPtr extends Type<TypeFunPtr> implements Cyclic {
  // List of known functions in set, or 'flip' for choice-of-functions.
  // A single bit is a classic code pointer.
  public BitsFun _fidxs;        // Known function bits
  public int _nargs;            // Number of formals, including the display
  public Type _dsp;             // Display; is_display_ptr
  public Type _ret;             // Return scalar type
  boolean _cyclic; // Type is cyclic.  This is a summary property, not a part of the type, hence is not in the equals nor hash

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
    _fidxs.str(sb);
    sb.p('{');                  // Collection (even of 1) start
    if( debug ) _dsp.str(sb,dups,mem,debug).p(' ');
    sb.p("->");
    _ret.str(sb,dups,mem,debug).p(' ');
    return sb.p('}');
  }

  public String names(boolean debug) { return FunNode.names(_fidxs,new SB(),debug).toString(); }

  static { new Pool(TFUNPTR,new TypeFunPtr()); }
  public static TypeFunPtr make( BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    // Assert the fidxs do not appear in the chain of returns.
    Type x = ret;
    while( x instanceof TypeFunPtr ) {
      TypeFunPtr xfp = (TypeFunPtr)x;
      assert !fidxs.overlaps(xfp._fidxs);
      if( xfp._ret==xfp ) break; // Self-cycle ends search
      x = xfp._ret;
    }
    assert dsp.is_display_ptr(); // Simple display ptr.  Just the alias.
    return malloc(fidxs,nargs,dsp,ret).hashcons_free();
  }

  // Preserve the invariant that the fidxs do not appear in the chain of
  // returns, by converting to a cyclic type or otherwise rolling-up the return
  // chain.  Prevents infinitely long types, very similarly to the TypeStruct
  // approx call, except the problem is much simpler.

  // If the return-chain contains an instance of fidxs, we approximate to
  // prevent the same fidx appearing twice.

  // Scan 1: Follow chain to the end and return either the repeat point or
  // null.  If no repeats, build the TFP as usual.  If repeating, also gather
  // all FIDXS seen.
  //
  // Scan 2: Follow the repeat point to the end, and return either all the
  // FIDXS seen if the end is high/cycle, or null otherwise.  If ends high/
  // cycle build a length-1 cycle from all FIDXS.
  //
  // Scan 3: starting both from the repeat point and the start, recurse until
  // one or both are LOW.  Return (LOW meet other), and unwind the recursion
  // wrapping merged TFPs as we go.
  //
  static private BitsFun _SCAN1_FIDXS;
  static public TypeFunPtr make0( BitsFun fidxs, int nargs, Type dsp, Type tret ) {
    _SCAN1_FIDXS = null;        // Reset
    TypeFunPtr trepeat = _scan1(fidxs,tret);
    if( trepeat==null )
      return make(fidxs,nargs,dsp,tret);   // build as usual
    BitsFun scan2_fidxs = trepeat._scan2();
    if( scan2_fidxs!=null )
      return make_recursive(fidxs.meet(_SCAN1_FIDXS),nargs,dsp);  // build a 1-cycle
    assert fidxs.overlaps(trepeat._fidxs);
    // The final meet
    Type mdsp = dsp.meet(trepeat._dsp);
    int mnargs = Math.min(nargs,trepeat._nargs);
    Type mret = _scan3(tret,trepeat._ret);
    return make(fidxs.meet(trepeat._fidxs),mnargs,mdsp,mret);
  }

  // Scan 1: Follow chain to the end and return either the repeat point or
  // null.  If no repeats, build the TFP as usual.  If repeating, also gather
  // all FIDXS seen.
  static private TypeFunPtr _scan1( BitsFun fidxs, Type tret ) {
    if( !(tret instanceof TypeFunPtr) )
      return null; // The end, no repeats, valid as-is.
    TypeFunPtr tfret = (TypeFunPtr)tret;
    // Check for repeats
    if( fidxs.overlaps(tfret._fidxs) ) {
      assert _SCAN1_FIDXS == null;
      _SCAN1_FIDXS = tfret._fidxs;
      return tfret;             // The repeat point
    }
    // Hit a cyclic-end, with no repeats.  Counts as a high-end
    if( tfret._ret == tfret )
      return null;              // The end, no repeats
    // Carry on the recursion
    TypeFunPtr tfp = _scan1(fidxs,tfret._ret);
    if( tfp==null ) return null; // Found the end, valid as-is
    _SCAN1_FIDXS = _SCAN1_FIDXS.meet(tfret._fidxs); // Gather fidxs on the unwind
    return tfp;
  }

  // Scan 2: Follow the repeat point to the end, and return either all the
  // FIDXS seen if the end is high/cycle, or null otherwise.  If ends high/
  // cycle build a length-1 cycle from all FIDXS.
  private BitsFun _scan2() {
    if( !(_ret instanceof TypeFunPtr) )
      // If high, making a cycle.  If low, moving on to scan3.
      return _ret.above_center() ? BitsFun.EMPTY : null;
    TypeFunPtr tfret = (TypeFunPtr)_ret;
    if( tfret._ret==tfret )     // Ending cycle?
      return tfret._fidxs;      // Ending high/cycle, return FIDXS
    // Need to keep scanning here
    throw unimpl();
  }

  // Scan 3: starting both from the repeat point and the start, recurse until
  // one or both are LOW.  Return (LOW meet other), and unwind the recursion
  // wrapping merged TFPs as we go.
  static private Type _scan3(Type t0, Type t1) {
    if( t0 instanceof TypeFunPtr && t1 instanceof TypeFunPtr )
      throw unimpl();
    Type mt = t0.meet(t1);
    assert !(mt instanceof TypeFunPtr); // Since low ending, the meet never falls to a TFP
    return mt;
  }

  // Allocate and init
  private static TypeFunPtr malloc(BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(fidxs,nargs,dsp,ret);
  }

  // Make self recursive
  static private TypeFunPtr make_recursive( BitsFun fidxs, int nargs, Type dsp ) {
    TypeFunPtr tfp = malloc(fidxs,nargs,Type.ANY,null);
    tfp._ret = tfp;
    tfp._hash = tfp.compute_hash();
    TypeFunPtr old = (TypeFunPtr)tfp.intern_lookup();
    if( old!=null )             // Return prior hit
      return POOLS[TFUNPTR].free(tfp,old);
    tfp.rdual();
    if( tfp.retern() != tfp.dual() ) tfp.dual().retern();
    return tfp;
  }

  public static TypeFunPtr make( int fidx, int nargs, Type dsp, Type ret ) { return make(BitsFun.make0(fidx),nargs,dsp,ret); }
  public static TypeFunPtr make_new_fidx( int parent, int nargs, Type dsp, Type ret ) { return make(BitsFun.make_new_fidx(parent),nargs,dsp,ret); }
  public static TypeFunPtr make( BitsFun fidxs, int nargs) { return make(fidxs,nargs,TypeMemPtr.NO_DISP,Type.SCALAR); }
  public        TypeFunPtr make_from( TypeMemPtr dsp ) { return make(_fidxs,_nargs, dsp,_ret); }
  public        TypeFunPtr make_from( BitsFun fidxs  ) { return fidxs==_fidxs ? this : make( fidxs,_nargs,_dsp,_ret); }
  public        TypeFunPtr make_from_ret( Type ret  ) { return make( _fidxs,_nargs,_dsp,ret); }
  public        TypeFunPtr make_from( Type dsp, Type ret ) { return make(_fidxs,_nargs, dsp,ret); }
  public        TypeFunPtr make_no_disp( ) { return make(_fidxs,_nargs,TypeMemPtr.NO_DISP,_ret); }
  public static TypeMemPtr DISP = TypeMemPtr.DISPLAY_PTR; // Open display, allows more fields

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.FULL ,1,Type.ALL,Type.ALL);
  public  static final TypeFunPtr EMPTY  =         make(BitsFun.EMPTY,0,Type.ANY,Type.ANY);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,EMPTY.dual()};

  @Override protected TypeFunPtr xdual() {
    return malloc(_fidxs.dual(),_nargs,_dsp.dual(),_ret.dual());
  }
  @Override protected TypeFunPtr rdual() {
    assert _hash==compute_hash();
    if( _dual != null ) return _dual;
    TypeFunPtr dual = _dual = malloc(_fidxs.dual(),_nargs,null,null);
    dual._dual = this;          // Stop the recursion
    dual._dsp = _dsp.rdual();
    dual._hash = dual.compute_hash();
    dual._ret = _ret.rdual();
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TFUNPTR:break;
    case TFUNSIG: return t.xmeet(this);
    case TFLT:
    case TINT:
    case TMEMPTR:
    case TRPC:   return cross_nil(t);
    case TARY:
    case TLIVE:
    case TOBJ:
    case TSTR:
    case TSTRUCT:
    case TTUPLE:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeFunPtr tf = (TypeFunPtr)t;
    BitsFun fidxs = _fidxs.meet(tf._fidxs);
    // Recursive but not cyclic; since at least one of these types is
    // non-cyclic normal recursion will bottom-out.

    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    TypeFunPtr min_nargs = _nargs < tf._nargs ? this : tf;
    TypeFunPtr max_nargs = _nargs < tf._nargs ? tf : this;
    int nargs = min_nargs.above_center() ? max_nargs._nargs : min_nargs._nargs;
    Type dsp = _dsp.meet(tf._dsp);
    // If both are short cycles, the result is a short cycle
    if( _ret==this && tf._ret==tf )
      return make_recursive(fidxs,nargs,dsp);
    // Otherwise, recursively find the return
    Type ret = _ret.meet(tf._ret);
    return make0(fidxs,nargs,dsp,ret);
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit

  // Widens, not lowers.
  @Override public TypeFunPtr simple_ptr() {
    Type ds = _dsp.simple_ptr();
    Type rs = _ret.simple_ptr();
    if( _dsp==ds && _ret==rs ) return this;
    return make_from(ds,rs);
  }

  @Override public boolean above_center() { return _fidxs.above_center() || (_fidxs.is_con() && _dsp.above_center()); }
  @Override public boolean may_be_con()   {
    return _dsp.may_be_con() &&
      _fidxs.abit() != -1 &&
      !is_forward_ref();
  }
  @Override public boolean is_con()       {
    return _dsp==TypeMemPtr.NO_DISP && // No display (could be constant display?)
      // Single bit covers all functions (no new children added, but new splits
      // can appear).  Currently, not tracking this at the top-level, so instead
      // just triggering off of a simple heuristic: a single bit above BitsFun.FULL.
      _fidxs.abit() > 1 &&
      !is_forward_ref();
  }
  @Override public boolean must_nil() { return _fidxs.test(0) && !_fidxs.above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make_from(bits);
  }
  @Override public Type meet_nil(Type nil) {
    assert nil==NIL || nil==XNIL;
    // See testLattice15.  The UNSIGNED NIL tests as a lattice:
    //    [~0]->~obj  ==>  NIL  ==>  [0]-> obj
    // But loses the pointed-at type down to OBJ.
    // So using SIGNED NIL, which also tests as a lattice:
    //    [~0]->~obj ==>  XNIL  ==>  [0]->~obj
    //    [~0]-> obj ==>   NIL  ==>  [0]-> obj

    if( _fidxs.isa(BitsFun.NIL.dual()) ) {
      if( _dsp==DISP.dual() && nil==XNIL )  return XNIL;
      if( nil==NIL ) return NIL;
    }
    return make(_fidxs.meet(BitsFun.NIL),_nargs,
                nil==NIL ? TypeMemPtr.DISP_SIMPLE : _dsp,
                _ret);
  }
  // Used during approximations, with a not-interned 'this'.
  // Updates-in-place.
  public Type ax_meet_nil(Type nil) {
    throw com.cliffc.aa.AA.unimpl();
  }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  @Override public byte isBitShape(Type t) {
    if( t._type == TNIL ) return 0;                  // Dead arg is free
    if( t._type == TSCALAR ) return 0;               // Scalar is OK
    return (byte)(t instanceof TypeFunPtr ? 0 : 99); // Mixing TFP and a non-ptr
  }
  @SuppressWarnings("unchecked")
  @Override public void walk( Predicate<Type> p ) { if( p.test(this) ) { _dsp.walk(p); _ret.walk(p); } }

  // Generic functions
  public boolean is_forward_ref() {
    if( _fidxs.abit() <= 1 ) return false; // Multiple fidxs, or generic fcn ptr
    FunNode fun = FunNode.find_fidx(Math.abs(fidx()));
    return fun != null && fun.is_forward_ref();
  }
  TypeFunPtr _sharpen_clone(TypeMemPtr dsp) {
    TypeFunPtr tf = copy();
    tf._dsp = dsp;
    return tf;
  }
  @Override public TypeFunPtr widen() { return GENERIC_FUNPTR; }

  @Override public Type make_from(Type head, TypeMem map, VBitSet visit) {
    throw unimpl();
  }

  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) {
    //return _dsp.repeats_in_cycles(head,bs);
    throw unimpl();
  }

  @Override public boolean is_display_ptr() { return _dsp.is_display_ptr(); }

  // All reaching fidxs, including any function returns
  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    if( Type.ARF.tset(_uid) ) return _fidxs;
    // Myself, plus any function returns
    return _fidxs.meet(_ret._all_reaching_fidxs(tmem));
  }  

}
