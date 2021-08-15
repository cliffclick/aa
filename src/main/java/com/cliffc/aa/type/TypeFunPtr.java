package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import static com.cliffc.aa.AA.unimpl;

import java.util.function.Predicate;


/**
 * Function indices or function pointers; a single instance can include all
 * possible aliased function pointers.  Function pointers can be executed, are
 * not GC'd, and cannot be Loaded or Stored through (although they can be
 * loaded & stored).
 * A TypeFunPtr includes a set of function indices and the display and NOT
 * e.g. the function arguments nor formals.  Formals are stored in the FunNode.
 * Each function index (or fidx) is a constant value, a classic code pointer.
 * Cloning the code immediately also splits the fidx with a new fidx bit for
 * both the original and the new code.
 */
public final class TypeFunPtr extends Type<TypeFunPtr> {
  // List of known functions in set, or 'flip' for choice-of-functions.
  // A single bit is a classic code pointer.
  public BitsFun _fidxs;        // Known function bits
  public int _nargs;            // Number of formals, including the display
  public Type _disp;            // Display; is_display_ptr

  private TypeFunPtr init(BitsFun fidxs, int nargs, Type disp ) {
    super.init(TFUNPTR,"");
    _fidxs = fidxs; _nargs=nargs; _disp=disp;
    return this;
  }
  @Override int compute_hash() {
    assert _disp._hash != 0;    // Part of a cyclic hash
    return (TFUNPTR + _fidxs._hash + _nargs + _disp._hash)|256;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    return _fidxs==tf._fidxs && _nargs == tf._nargs && _disp==tf._disp;
  }
  // Structs can contain TFPs in fields, and TFPs contain a Struct, but never
  // in a cycle.
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    if( _fidxs!=tf._fidxs || _nargs != tf._nargs ) return false;
    return _disp==tf._disp || _disp.cycle_equals(tf._disp);
  }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    _fidxs.str(sb);
    sb.p('{');                  // Collection (even of 1) start
    if( debug ) _disp.str(sb,dups,mem,debug).p(' ');
    return sb.p('}');
  }

  public String names(boolean debug) { return FunNode.names(_fidxs,new SB(),debug).toString(); }

  static { new Pool(TFUNPTR,new TypeFunPtr()); }
  public static TypeFunPtr make( BitsFun fidxs, int nargs, Type disp ) {
    assert disp.is_display_ptr(); // Simple display ptr.  Just the alias.
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(fidxs,nargs,disp).hashcons_free();
  }

  public static TypeFunPtr make( int fidx, int nargs, Type disp ) { return make(BitsFun.make0(fidx),nargs,disp); }
  public static TypeFunPtr make_new_fidx( int parent, int nargs, Type disp ) { return make(BitsFun.make_new_fidx(parent),nargs,disp); }
  public        TypeFunPtr make_from( TypeMemPtr disp ) { return make(_fidxs,_nargs,disp); }
  public        TypeFunPtr make_from( BitsFun fidxs ) { return make(fidxs,_nargs,_disp); }
  public        TypeFunPtr make_no_disp( ) { return make(_fidxs,_nargs,TypeMemPtr.NO_DISP); }
  public static TypeMemPtr DISP = TypeMemPtr.DISPLAY_PTR; // Open display, allows more fields

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.FULL,1,Type.ALL);
  public  static final TypeFunPtr EMPTY  = make(BitsFun.EMPTY,0,TypeMemPtr.NO_DISP);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,EMPTY.dual()};

  @Override protected TypeFunPtr xdual() {
    return new TypeFunPtr().init(_fidxs.dual(),_nargs,_disp.dual());
  }
  @Override protected TypeFunPtr rdual() {
    if( _dual != null ) return _dual;
    TypeFunPtr dual = _dual = new TypeFunPtr().init(_fidxs.dual(),_nargs,_disp.rdual());
    if( _hash != 0 ) {
      assert _hash == compute_hash();
      dual._hash = dual.compute_hash(); // Compute hash before recursion
    }
    dual._dual = this;
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
    return make(fidxs,nargs,_disp.meet(tf._disp));
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit

  @Override public boolean above_center() { return _fidxs.above_center() || (_fidxs.is_con() && _disp.above_center()); }
  @Override public boolean may_be_con()   {
    return _disp.may_be_con() &&
      _fidxs.abit() != -1 &&
      !is_forward_ref();
  }
  @Override public boolean is_con()       {
    return _disp==TypeMemPtr.NO_DISP && // No display (could be constant display?)
      // Single bit covers all functions (no new children added, but new splits
      // can appear).  Currently not tracking this at the top-level, so instead
      // just triggering off of a simple heuristic: a single bit above BitsFun.FULL.
      _fidxs.abit() > 1 &&
      !is_forward_ref();
  }
  @Override public boolean must_nil() { return _fidxs.test(0) && !_fidxs.above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make(bits,_nargs,_disp);
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
      if( _disp==DISP.dual() && nil==XNIL )  return XNIL;
      if( nil==NIL ) return NIL;
    }
    return make(_fidxs.meet(BitsFun.NIL),_nargs,nil==NIL ? TypeMemPtr.DISP_SIMPLE : _disp);
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
  @Override public void walk( Predicate<Type> p ) { if( p.test(this) ) { _disp.walk(p); } }

  // Generic functions
  public boolean is_forward_ref() {
    if( _fidxs.abit() <= 1 ) return false; // Multiple fidxs, or generic fcn ptr
    FunNode fun = FunNode.find_fidx(Math.abs(fidx()));
    return fun != null && fun.is_forward_ref();
  }
  TypeFunPtr _sharpen_clone(TypeMemPtr disp) {
    TypeFunPtr tf = (TypeFunPtr)clone();
    tf._disp = disp;
    tf._hash = tf.compute_hash();
    return tf;
  }
  @Override public TypeFunPtr widen() { return GENERIC_FUNPTR; }

  @Override public Type make_from(Type head, TypeMem map, VBitSet visit) {
    throw unimpl();
  }

}
