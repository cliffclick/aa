package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

// Function indices or function pointers; a single instance can include all
// possible aliased function pointers.  Function pointers can be executed, are
// not GC'd, and cannot be Loaded or Stored through (although they can be
// loaded & stored).
//
// A TypeFunPtr includes a set of function indices, plus the formal argument
// types.  Included in the formal arguments are pointers to all upwards exposed
// closures.  These have special names to indicate they are not part of the
// user-defined arguments.
//
// Each function index (or fidx) is a constant value, a classic code pointer.
// Cloning the code immediately also splits the fidx with a new fidx bit for
// both the original and the new code.
//
// The formal function signature is used to e.g. check formal call args, during
// call resolution, and on TypeNodes for function arg types.  CallNodes use
// this type to check their incoming arguments, although their return values
// (including memory) come from the Ret itself, not the Fun and not this type.

public final class TypeFunPtr extends Type<TypeFunPtr> {
  // List of known functions in set, or 'flip' for choice-of-functions.
  // A single bit is a classic code pointer.
  BitsFun _fidxs;       // Known function bits

  // Union (or join) signature of said functions; depends on if _fidxs is
  // above_center() or not.  Slot 0 is the return type.  Slot 1 is for the
  // display type, is always "is_display()" and either TypeMemPtr or NIL.
  public TypeStruct _args;      // Standard args, zero-based, no memory

  boolean _cyclic; // Type is cyclic.  This is a summary property, not a description of value sets, hence is not in the equals or hash

  private TypeFunPtr(BitsFun fidxs, TypeStruct args ) { super(TFUNPTR); init(fidxs,args); }
  private void init (BitsFun fidxs, TypeStruct args ) { _fidxs = fidxs; _args=args; }
  @Override int compute_hash() { assert _args._hash != 0;  return TFUNPTR + _fidxs._hash + _args._hash; }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    return _fidxs==tf._fidxs && _args==tf._args;
  }
  // Structs can contain TFPs in fields, and TFPs contain a Struct, but never
  // in a cycle.
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    if( _fidxs!=tf._fidxs ) return false;
    return _args==tf._args || _args.cycle_equals(tf._args);
  }
  @Override public String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    String s = "*"+names()+"{ ";
    int len = _args._ts.length;
    for( int i=1; i<len; i++ )
      s += _args._flds[i]+":"+_args._ts[i].str(dups)+" ";
    s += "-> "+_args._ts[0].str(dups)+" }";
    return s;
  }

  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    sb.p('*').p(names()).p(":");
    return _args.dstr(sb,dups);
  }
  public String names() { return FunNode.names(_fidxs,new SB()).toString(); }
  public int nargs() { return _args._ts.length; }

  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr ret ) { FREE=this; return ret; }
  public static TypeFunPtr make( BitsFun fidxs, TypeStruct args ) {
    assert Util.eq(args._flds[0],"->"); // First is return
    assert args.at(1).is_display_ptr(); // Second is the display
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(fidxs,args);
    else {   FREE = null;        t1.init(fidxs,args); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Used by testing only
  public static TypeFunPtr make_new(TypeStruct args) { return make(BitsFun.make_new_fidx(BitsFun.ALL),args); }
  public TypeFunPtr make_fidx( int fidx ) { return make(BitsFun.make0(fidx),_args); }
  public TypeFunPtr make_new_fidx( int parent, TypeStruct args ) { return make(BitsFun.make_new_fidx(parent),args); }
  public static TypeStruct ARGS = TypeStruct.make_args(TypeAry.ts(Type.SCALAR,TypeMemPtr.DISPLAY_PTR));
  public static TypeFunPtr make_anon() { return make_new(ARGS); } // Make a new anonymous function ptr
  // Make a TFP with a new display and return value, used by FunPtrNode
  public TypeFunPtr make(Type display_ptr, Type ret) {
    assert _args.at(1).is_display_ptr() && display_ptr.is_display_ptr();
    TypeStruct args = _args.set_fld(0,ret        ,_args.fmod(0));
    args            =  args.set_fld(1,display_ptr,_args.fmod(1));
    return make(_fidxs,args);
  }
  public TypeFunPtr make_high_fidx() {
    if( _fidxs.above_center() ) return this;
    return make(_fidxs.dual(),_args);
  }

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.FULL,ARGS);
  private static final TypeFunPtr TEST_INEG = make(BitsFun.make0(2),TypeStruct.INT64__INT64);
  public  static final TypeFunPtr EMPTY = make(BitsFun.EMPTY,ARGS.dual());
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,TEST_INEG};

  @Override protected TypeFunPtr xdual() { return new TypeFunPtr(_fidxs.dual(),_args.dual()); }
  @Override protected TypeFunPtr rdual() {
    if( _dual != null ) return _dual;
    TypeFunPtr dual = _dual = new TypeFunPtr(_fidxs.dual(),_args.rdual());
    dual._dual = this;
    dual._hash = dual.compute_hash();
    dual._cyclic = true;
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TFUNPTR:break;
    case TFLT:
    case TINT:
    case TMEMPTR:
    case TRPC:   return cross_nil(t);
    case TFUN:
    case TTUPLE:
    case TOBJ:
    case TSTR:
    case TSTRUCT:
    case TMEM:   return ALL;
    case TNIL:                  // TODO: Meet-with-NIL can return NIL is some cases
    default: throw typerr(t);   // All else should not happen
    }
    TypeFunPtr tf = (TypeFunPtr)t;
    // Function args are MEET during MEET
    return make(_fidxs.meet(tf._fidxs),(TypeStruct)_args.meet(tf._args));
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit
  public Type arg(int idx) { return _args.at(idx); }
  public Type ret() { return _args.at(0); }
  public TypeMemPtr display() { return (TypeMemPtr)_args.at(1); } // Always a Display pointer or NIL

  @Override public boolean above_center() { return _fidxs.above_center(); }
  @Override public boolean may_be_con()   { return above_center(); }
  // Since fidxs may split, never a constant.
  @Override public boolean is_con()       { return false; }
  @Override public boolean must_nil() { return _fidxs.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make(bits,_args);
  }
  @Override public Type meet_nil() {
    if( _fidxs.test(0) )      // Already has a nil?
      return _fidxs.above_center() ? NIL : this;
    return make(_fidxs.meet(BitsFun.NIL),_args);
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
  @Override void walk( Predicate<Type> p ) { if( p.test(this) ) { _args.walk(p); } }
  // Keep the high parts
  @Override public Type startype() {
    BitsFun fidxs  = _fidxs.startype();
    TypeStruct args= _args .startype();
    return make(fidxs,args);
  }

  // Generic functions
  public boolean is_forward_ref() {
    if( _fidxs.abit() == -1 ) return false; // Multiple fidxs
    if( _fidxs.getbit() == 1 ) return false; // Thats the generic function ptr
    FunNode fun = FunNode.find_fidx(Math.abs(fidx()));
    return fun != null && fun.is_forward_ref();
  }
}
