package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.DSP_IDX;

// Function signatures: formal arguments (and return) used to type-check.  This
// is NOT any "code pointer" or "function index" or "fidx"; see TypeFunPtr.
public final class TypeFunSig extends Type<TypeFunSig> {
  public TypeStruct _formals;   // Display2, Arg3, Arg4, ... (no memory)
  public Type _ret;             // Plain return type (no memory)

  private TypeFunSig init(TypeStruct formals, Type ret ) {
    super.init("");
    TypeFld disp=null;
    assert (disp=formals.get("^")) == null || disp.is_display_ptr();
    assert formals.get(" mem")==null; // No memory
    _formals=formals;
    _ret=ret;
    return this;
  }
  @Override int compute_hash() {
    int hash=TFUNSIG + _formals._hash + _ret._hash;
    return hash==0 ? TFUNSIG : hash;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunSig) ) return false;
    TypeFunSig tf = (TypeFunSig)o;
    return _formals==tf._formals && _ret==tf._ret;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( debug ) sb.p('_').p(_uid);
    sb.p(_name);
    sb.p("{ ");
    for( TypeFld arg : _formals.osorted_flds() ) {
      sb.p(arg._fld);
      if( arg._t != Type.SCALAR )
        arg._t.str(sb.p(':'),dups,mem,debug);
      sb.p(' ');
    }
    return _ret.str(sb.p("-> "),dups,mem,debug).p("}");
  }

  static { new Pool(TFUNSIG,new TypeFunSig()); }
  public static TypeFunSig make( TypeStruct formals, Type ret ) {
    TypeFunSig t1 = POOLS[TFUNSIG].malloc();
    return t1.init(formals,ret).hashcons_free();
  }

  public static TypeFunSig make1( Type arg1 ) { return make(TypeStruct.args(arg1),Type.SCALAR); }
  public static TypeFunSig make2( Type arg1, Type arg2 ) { return make(TypeStruct.args(arg1,arg2),Type.SCALAR); }
  public TypeFunSig make_from( TypeStruct formals ) { return make(formals,_ret); }
  public TypeFunSig make_from_arg( TypeFld arg ) { return make(_formals.replace_fld(arg),_ret); }
  public TypeFunSig make_from_remove( String fld ) { return make(_formals.del_fld(fld),_ret); }

  public static final TypeFunSig II_I = make(TypeStruct.INT64_INT64,TypeInt.INT64);
  static final TypeFunSig[] TYPES = new TypeFunSig[]{II_I};

  public TypeFld arg(int idx) { return _formals.fld_idx(idx); }
  public Type display() { return arg(DSP_IDX); }

  @Override protected TypeFunSig xdual() {  return POOLS[TFUNSIG].<TypeFunSig>malloc().init(_formals.dual(),_ret.dual()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TFUNSIG: break;
    case TFUNPTR:
      return ALL;               // Not supposed to mix TypeFunPtr and TypeFunSig
    case TARY:
    case TFLT:
    case TINT:
    case TLIVE:
    case TMEM:
    case TMEMPTR:
    case TOBJ:
    case TRPC:
    case TSTR:
    case TSTRUCT:
    case TTUPLE:
      return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeFunSig tf = (TypeFunSig)t;
    return make((TypeStruct)_formals.meet(tf._formals),_ret.meet(tf._ret));
  }

  @Override public boolean above_center() { return _formals.above_center(); }
  @Override public boolean may_be_con()   { return above_center(); }
  @Override public boolean is_con()       { return false; }
  @Override public boolean must_nil()     { return false; }
  @Override public boolean may_nil()      { return false; }
  @Override Type not_nil() { return this; }
  @Override public Type meet_nil(Type nil) { return Type.SCALAR; }
  @Override public byte isBitShape(Type t) { return 99; }
}
