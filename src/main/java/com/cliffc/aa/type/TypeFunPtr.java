package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;
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
  public Type _disp;            // Display; is_display_ptr

  // Include a classic set of args/ret type, where a MEET of TFPs JOINS the
  // args and MEETS the rets.  The bottom type takes nothing (all XSCALAR args)
  // and returns anything (SCALAR).  Contrast this to the observed parameters
  // to a FunNode + ParmNodes; here we take the MEET of actuals, and the return
  // is computed.  Currently only used by H-M prototype.
  
  // TODO: Move _nargs and _disp into this; _disp is currently the observed actuals.
  // TODO: Move Control and Memory into this, use the unified indices.
  public Type[] _args;
  public Type _ret;

  private TypeFunPtr(BitsFun fidxs, int nargs, Type disp, Type[] args, Type ret ) { super(TFUNPTR); init(fidxs,nargs,disp,args,ret); }
  private void init (BitsFun fidxs, int nargs, Type disp, Type[] args, Type ret ) { _fidxs = fidxs; _nargs=nargs; _disp=disp; _args=args; _ret=ret; }
  @Override int compute_hash() {
    assert _disp._hash != 0;    // Part of a cyclic hash
    // TODO: Someday a TFP takes a TFP arg, and so needs the cyclic-hash treatment.
    int hash = 0;
    for( Type t : _args ) { assert t._hash!=0; hash += t._hash; }
    // TODO: Need to handle cycles for recursive fcns
    return (TFUNPTR + _fidxs._hash + _nargs + _disp._hash + _ret._hash + hash)|256;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    // TODO: Need to handle cycles for recursive fcns
    return _fidxs==tf._fidxs && _nargs == tf._nargs && _disp==tf._disp && _ret==tf._ret && _args==tf._args;
  }
  // Structs can contain TFPs in fields, and TFPs contain a Struct, but never
  // in a cycle.
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    if( _fidxs!=tf._fidxs || _nargs != tf._nargs ) return false;
    // TODO: Need to handle cycles for recursive fcns
    if( _ret!=tf._ret || _args != tf._args ) return false;
    return _disp==tf._disp || _disp.cycle_equals(tf._disp);
  }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    _fidxs.str(sb);
    sb.p('{');                  // Collection (even of 1) start
    if( debug ) _disp.str(sb,dups,mem,debug).p(' ');
    for( Type t : _args ) t.str(sb,dups,mem,debug).p(' ');
    return _ret.str(sb.p("-> "),dups,mem,debug).p('}');
  }

  public String names(boolean debug) { return FunNode.names(_fidxs,new SB(),debug).toString(); }

  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr ret ) { FREE=this; return ret; }
  private static TypeFunPtr make( BitsFun fidxs, int nargs, Type disp, Type[] args, Type ret ) {
    assert disp.is_display_ptr(); // Simple display ptr.  Just the alias.
    // TODO: Need to break this apart for cyclic function ptrs
    Type[] args2 = Types.hash_cons(args);
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(fidxs,nargs,disp,args2,ret);
    else {   FREE = null;        t1.init(fidxs,nargs,disp,args2,ret); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeFunPtr make( BitsFun fidxs, int nargs, Type disp ) {
    Type[] args = Types.get(nargs);
    Arrays.fill(args,Type.XSCALAR);
    return make(fidxs,nargs,disp,args, Type.SCALAR);
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
    Type[] args = Types.get(_args.length);
    for( int i=0; i<args.length; i++ ) args[i] = _args[i].dual();
    args = Types.hash_cons(args);
    return new TypeFunPtr(_fidxs.dual(),_nargs,_disp.dual(),args,_ret.dual());
  }
  @Override protected TypeFunPtr rdual() {
    if( _dual != null ) return _dual;
    Type[] args = Types.get(_args.length);
    TypeFunPtr dual = _dual = new TypeFunPtr(_fidxs.dual(),_nargs,_disp.rdual(),args,_ret.rdual());
    if( _hash != 0 ) {
      assert _hash == compute_hash();
      dual._hash = dual.compute_hash(); // Compute hash before recursion
    }
    for( int i=0; i<args.length; i++ ) args[i] = _args[i].rdual();
    dual._args = Types.hash_cons(args); // hashcons cyclic arrays
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
    Type[] args = _args.length <= tf._args.length ? argmeet(tf) : tf.argmeet(this);
    TypeFunPtr min_nargs = _nargs < tf._nargs ? this : tf;
    TypeFunPtr max_nargs = _nargs < tf._nargs ? tf : this;
    int nargs = min_nargs.above_center() ? max_nargs._nargs : min_nargs._nargs;
    assert nargs==args.length; // TODO: Remove nargs calc, because i think this should be true
    return make(fidxs,nargs,_disp.meet(tf._disp),args,_ret.meet(tf._ret));
  }
  // Meet 2 arg arrays, shorter is in 'this'.
  private Type[] argmeet( TypeFunPtr tmax ) {
    int len = above_center() ? tmax._args.length : _args.length;
    // Meet of common elements
    Type[] args = Types.get(len);
    for( int i=0; i<_args.length; i++ )
      args[i] = _args[i].join(tmax._args[i]); // Recursive not cyclic
    // Elements only in the longer args; the short args must be high and so
    // is effectively infinitely extended with high fields.
    for( int i=_args.length; i<len; i++ )
      args[i] = tmax._args[i];
    return Types.hash_cons(args);
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit

  @Override public boolean above_center() { return _fidxs.above_center() || (_fidxs.is_con() && _disp.above_center()); }
  @Override public boolean may_be_con()   { return above_center() || is_con(); }
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
    return bits==_fidxs ? this : make(bits,_nargs,_disp,_args,_ret);
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
    return make(_fidxs.meet(BitsFun.NIL),_nargs,nil==NIL ? TypeMemPtr.DISP_SIMPLE : _disp, _args,_ret);
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
}
