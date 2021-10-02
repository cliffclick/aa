package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.DSP_IDX;
import static com.cliffc.aa.AA.MEM_IDX;

// Function signatures: formal arguments (and return) used to type-check.  This
// is NOT any "code pointer" or "function index" or "fidx"; see TypeFunPtr.
public final class TypeFunSig extends Type<TypeFunSig> {
  public TypeStruct _formals;   // Control0, Memory1, Display2, Arg3, Arg4, ...
  private int _max_arg;

  private TypeFunSig init(TypeStruct formals, TypeTuple ret ) {
    super.init(TFUNSIG,"");
    TypeFld disp=null;
    assert (disp=formals.fld_find("^")) == null || disp.is_display_ptr();
    assert ret.len()==3 && ret.at(MEM_IDX) instanceof TypeMem;
    _formals=formals;
    _max_arg = DSP_IDX;
    for( TypeFld arg : _formals.flds() )
      _max_arg = Math.max(_max_arg,arg._order);
    return this;
  }
  @Override int compute_hash() {
    int hash=TFUNSIG + _formals._hash;
    return hash==0 ? 3 : hash;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunSig) ) return false;
    TypeFunSig tf = (TypeFunSig)o;
    return _formals==tf._formals;
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
    return sb.p("-> }");
  }

  static { new Pool(TFUNSIG,new TypeFunSig()); }
  public static TypeFunSig make( TypeStruct formals, TypeTuple ret ) {
    TypeFunSig t1 = POOLS[TFUNSIG].malloc();
    return t1.init(formals,ret).hashcons_free();
  }

  public static TypeFunSig make( TypeTuple ret, Type arg1 ) { return make(TypeStruct.args(arg1),ret); }
  public static TypeFunSig make( TypeTuple ret, Type arg1, Type arg2 ) { return make(TypeStruct.args(arg1,arg2),ret); }
  public TypeFunSig make_from( TypeStruct formals ) { return make(formals,TypeTuple.RET); }
  public TypeFunSig make_from_arg( TypeFld arg ) { return make(_formals.replace_fld(arg),TypeTuple.RET); }
  public TypeFunSig make_from_remove( String fld ) { return make(_formals.del_fld(fld),TypeTuple.RET); }


  public static final TypeFunSig II_I = make(TypeStruct.INT64_INT64, TypeTuple.make_ret(TypeInt.INT64));
  static final TypeFunSig[] TYPES = new TypeFunSig[]{II_I};

  public int nargs() { return _max_arg+1; }
  public TypeFld arg(int idx) { return _formals.fld_idx(idx); }
  public Type display() { return arg(DSP_IDX); }

  @Override protected TypeFunSig xdual() { return new TypeFunSig().init(_formals.dual(),TypeTuple.RET.dual()); }
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
    return make((TypeStruct)_formals.meet(tf._formals),TypeTuple.RET);
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
