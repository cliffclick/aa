package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

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
public final class TypeFunPtr extends Type<TypeFunPtr> {
  // List of known functions in set, or 'flip' for choice-of-functions.
  // A single bit is a classic code pointer.
  public BitsFun _fidxs;        // Known function bits
  public int _nargs;            // Number of formals, including the display
  public TypeMemPtr _disp;      // Display; is_display_ptr

  private TypeFunPtr(BitsFun fidxs, int nargs, TypeMemPtr disp ) { super(TFUNPTR); init(fidxs,nargs,disp); }
  private void init (BitsFun fidxs, int nargs, TypeMemPtr disp ) { _fidxs = fidxs; _nargs=nargs; _disp=disp; }
  @Override int compute_hash() { assert _disp._hash != 0;  return (TFUNPTR + _fidxs._hash + _nargs + _disp._hash)|256; }

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
  @Override public String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    return "*"+names(true)+"{"+_disp+"}";
  }

  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    sb.p('*').p(names(true)).p('{');
    return _disp.dstr(sb,dups).p('}');
  }
  public String names(boolean debug) { return FunNode.names(_fidxs,new SB(),debug).toString(); }

  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr ret ) { FREE=this; return ret; }
  public static TypeFunPtr make( BitsFun fidxs, int nargs, TypeMemPtr disp ) {
    assert disp.is_display_ptr(); // Simple display ptr.  Just the alias.
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(fidxs,nargs,disp);
    else {   FREE = null;        t1.init(fidxs,nargs,disp); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeFunPtr make( int fidx, int nargs, TypeMemPtr disp ) { return make(BitsFun.make0(fidx),nargs,disp); }
  public static TypeFunPtr make_new_fidx( int parent, int nargs, TypeMemPtr disp ) { return make(BitsFun.make_new_fidx(parent),nargs,disp); }
                TypeFunPtr make_from( TypeMemPtr disp ) { return make(_fidxs,_nargs,disp); }
  public static TypeMemPtr DISP = TypeMemPtr.DISPLAY_PTR; // Open display, allows more fields
  public static TypeMemPtr NO_DISP = TypeMemPtr.NO_DISP;

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.FULL,1,TypeMemPtr.DISP_SIMPLE);
  public  static final TypeFunPtr EMPTY = make(BitsFun.EMPTY,1,NO_DISP);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,EMPTY};

  @Override protected TypeFunPtr xdual() { return new TypeFunPtr(_fidxs.dual(),_nargs,_disp.dual()); }
  @Override protected TypeFunPtr rdual() {
    if( _dual != null ) return _dual;
    TypeFunPtr dual = _dual = new TypeFunPtr(_fidxs.dual(),_nargs,_disp.rdual());
    dual._dual = this;
    if( _hash != 0 ) dual._hash = dual.compute_hash();
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
    TypeFunPtr min_tf = _nargs < tf._nargs ? this : tf;
    TypeFunPtr max_tf = _nargs < tf._nargs ? tf : this;
    int nargs = (min_tf.above_center() || _fidxs==BitsFun.EMPTY) ? max_tf._nargs : min_tf._nargs;
    return make(fidxs,nargs,(TypeMemPtr)_disp.meet(tf._disp));
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit

  @Override public boolean above_center() { return _fidxs.above_center() || (_fidxs.is_con() && _disp.above_center()); }
  @Override public boolean may_be_con()   { return above_center(); }
  // Since fidxs may split, never a constant.
  @Override public boolean is_con()       { return false; }
  // Basically, a constant fidx that may be split.
  public boolean can_be_fpnode() {
    return (_disp==TypeFunPtr.NO_DISP || _disp._obj==TypeStr.NO_DISP) && // No display
      // Single function
      _fidxs.abit() > 1 && !BitsAlias.is_parent(_fidxs.abit());
  }
  @Override public boolean must_nil() { return _fidxs.test(0) && !_fidxs.above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make(bits,_nargs,_disp);
  }
  @Override public Type meet_nil(Type nil) {
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
  @Override void walk( Predicate<Type> p ) { if( p.test(this) ) { _disp.walk(p); } }

  // Generic functions
  public boolean is_forward_ref() {
    if( _fidxs.abit() == -1 ) return false; // Multiple fidxs
    if( _fidxs.getbit() == 1 ) return false; // Thats the generic function ptr
    FunNode fun = FunNode.find_fidx(Math.abs(fidx()));
    return fun != null && fun.is_forward_ref();
  }
  TypeFunPtr _sharpen_clone(TypeMemPtr disp) {
    TypeFunPtr tf = (TypeFunPtr)clone();
    tf._disp = disp;
    tf._hash = tf.compute_hash();
    return tf;
  }
  @Override TypeFunPtr crush_fld_impl(String fld) { return make(_fidxs,_nargs,_disp.crush_fld_impl(fld)); }
  @Override public TypeFunPtr widen() {
    // TODO: Widen to widened sigs
    return TypeFunPtr.GENERIC_FUNPTR;
  }
}
