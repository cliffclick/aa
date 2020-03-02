package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import java.util.BitSet;
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
  private BitsFun _fidxs;       // Known function bits

  // Union (or join) signature of said functions; depends on if _fidxs is
  // above_center() or not.  Slot 0 is for the display type, and so is always a
  // TypeMemPtr.
  public TypeStruct _args;      // Standard args, zero-based, no memory
  public Type _ret;             // Standard formal return type.

  private TypeFunPtr(BitsFun fidxs, TypeStruct args, Type ret ) { super(TFUNPTR); init(fidxs,args,ret); }
  private void init (BitsFun fidxs, TypeStruct args, Type ret ) { _fidxs = fidxs; _args=args; _ret=ret; }
  @Override int compute_hash() { return TFUNPTR + _fidxs._hash + _args._hash + _ret._hash; }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    return _fidxs==tf._fidxs && _args==tf._args && _ret==tf._ret;
  }
  // Structs can contain TFPs in fields, and TFPs contain a Struct, but never
  // in a cycle.
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public String str( VBitSet dups) {
    return "*"+names()+":{"+_args.str(dups)+"-> "+_ret.str(dups)+"}";}
  public String names() { return FunNode.names(_fidxs,new SB()).toString(); }
  public int nargs() { return _args._ts.length; }

  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr ret ) { FREE=this; return ret; }
  public static TypeFunPtr make( BitsFun fidxs, TypeStruct args, Type ret ) {
    assert args.at(0).isa(Type.NIL) || ((TypeMemPtr)args.at(0)).is_display();
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(fidxs,args,ret);
    else {   FREE = null;        t1.init(fidxs,args,ret); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Used by testing only
  public static TypeFunPtr make_new(TypeStruct args, Type ret) { return make(BitsFun.make_new_fidx(BitsFun.ALL),args,ret); }
  public TypeFunPtr make_fidx( int fidx ) { return make(BitsFun.make0(fidx),_args,_ret); }
  public TypeFunPtr make_new_fidx( int parent, TypeStruct args ) { return make(BitsFun.make_new_fidx(parent),args,_ret); }
  private static TypeStruct ARGS = TypeStruct.make_args(TypeStruct.ts(TypeMemPtr.DISPLAY_PTR));
  public static TypeFunPtr make_anon() { return make_new(ARGS,Type.SCALAR); } // Make a new anonymous function ptr
  // Make a TFP with a new display and return value, used by FunPtrNode
  public TypeFunPtr make(Type display, Type ret) {
    assert _args.is_display();
    assert display.isa(Type.NIL) || ((TypeMemPtr)display).is_display();
    return make(_fidxs,_args.set_fld(0,display,_args.fmod(0)),ret);
  }

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.FULL,ARGS,Type.SCALAR);
  private static final TypeFunPtr TEST_INEG = make(BitsFun.make0(2),TypeStruct.INT64,TypeInt.INT64);
  public  static final TypeFunPtr EMPTY = make(BitsFun.EMPTY,TypeStruct.SCALAR0,Type.XSCALAR);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,TEST_INEG};

  @Override protected TypeFunPtr xdual() { return new TypeFunPtr(_fidxs.dual(),_args.dual(),_ret.dual()); }
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
    return make(_fidxs.meet(tf._fidxs),(TypeStruct)_args.meet(tf._args),_ret.meet(tf._ret));
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit
  public Type arg(int idx) { return _args.at(idx); }
  public Type display() { return _args.at(0); } // Always a Display pointer or NIL
  public boolean is_class() { return _fidxs.is_class(); }

  @Override public BitsAlias recursive_aliases(BitsAlias abs, TypeMem mem) {
    if( _fidxs.test(1) ) return BitsAlias.NZERO; // All functions, all displays
    if( _fidxs.above_center() ) return abs;      // Choosing functions with no aliases
    BitSet bs = _fidxs.tree().plus_kids(_fidxs);
    for( int fidx = bs.nextSetBit(1); fidx >= 0; fidx = bs.nextSetBit(fidx+1) ) {
      BitsAlias cls = FunNode.find_fidx(fidx)._display_aliases;
      for( int alias : cls )
        abs = mem.recursive_aliases(abs,alias);
      if( abs.test(1) ) return abs; // Shortcut for already being full
    }
    return abs;
  }

  @Override public boolean above_center() { return _args.above_center(); }
  @Override public boolean may_be_con()   { return above_center() || is_con(); }
  @Override public boolean is_con()       {
    // More than 1 function being referred to
    if( _fidxs.abit() == -1 || is_class() ) return false;
    // All display bits have to be constants also
    for( int i=0; i<_args._ts.length; i++ )
      if( !_args._ts[i].is_con() )
        return false;
    return true;
  }
  @Override public boolean must_nil() { return _fidxs.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make(bits,_args,_ret);
  }
  @Override public Type meet_nil() {
    if( _fidxs.test(0) )      // Already has a nil?
      return _fidxs.above_center() ? NIL : this;
    return make(_fidxs.meet(BitsFun.NIL),_args,_ret);
  }
  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  @Override public byte isBitShape(Type t) {
    if( t._type == TNIL ) return 0;                   // Dead arg is free
    return (byte)(t instanceof TypeFunPtr ? 0 : -99); // Mixing TFP and a non-ptr
  }
  @SuppressWarnings("unchecked")
  @Override void walk( Predicate<Type> p ) { if( p.test(this) ) { _args.walk(p); _ret.walk(p); } }
  // Keep the high parts
  @Override public Type startype() {
    BitsFun fidxs  = _fidxs.startype();
    TypeStruct args= _args .startype();
    Type ret       = _ret  .startype();
    return make(fidxs,args,ret);
  }

  // Generic functions
  public boolean is_forward_ref() {
    if( _fidxs.abit() == -1 ) return false; // Multiple fidxs
    if( _fidxs.getbit() == 1 ) return false; // Thats the generic function ptr
    FunNode fun = FunNode.find_fidx(fidx());
    return fun != null && fun.is_forward_ref();
  }
}
