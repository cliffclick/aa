package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;
import static com.cliffc.aa.AA.*;

// Function signatures: formal arguments (and return) used to type-check.  This
// is NOT any "code pointer" or "function index" or "fidx"; see TypeFunPtr.
public final class TypeFunSig extends Type<TypeFunSig> {
  // Formal 0 is the Memory type, using TypeObj.ISUSED for ignored memory state.
  // Formal 1 is the Display pointer.
  // Formals 2-N are the normal arguments.
  public String[] _args;        // " mem", "^", ....
  public TypeTuple _formals;    // Control0, Memory1, Display2, Arg3, Arg4, ...
  public TypeTuple _ret;        // Control0, Memory1, Result2

  private TypeFunSig init (String[] args, TypeTuple formals, TypeTuple ret ) {
    super.init(TFUNSIG,"");
    assert args.length>=formals.len();
    assert (args[CTL_IDX]==null || Util.eq(args[CTL_IDX]," ctl")) && (formals.at(CTL_IDX)==Type.CTRL || formals.at(CTL_IDX)==Type.XCTRL);
    assert (args[MEM_IDX]==null || Util.eq(args[MEM_IDX]," mem")) && (formals.at(MEM_IDX) instanceof TypeMem || formals.at(MEM_IDX)==Type.ALL || formals.at(MEM_IDX)==Type.ANY);
    assert (args[DSP_IDX]==null || Util.eq(args[DSP_IDX],"^"   )) &&  formals.at(DSP_IDX).is_display_ptr();
    assert ret.len()==3 && ret.at(MEM_IDX) instanceof TypeMem;
    _args=args;
    _formals=formals;
    _ret=ret;
    return this;
  }
  @Override int compute_hash() {
    assert _formals._hash != 0;
    int hash=TFUNSIG + _formals._hash + _ret._hash;
    for( int i=0; i<_args.length; i++ ) i+=_args[i].hashCode();
    return hash==0 ? 3 : hash;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunSig) ) return false;
    TypeFunSig tf = (TypeFunSig)o;
    if( _formals!=tf._formals || _ret!=tf._ret || _args.length!=tf._args.length ) return false;
    if( _args == tf._args ) return true;
    for( int i=0; i<_args.length; i++ )
      if( !Util.eq(_args[i],tf._args[i]) )
        return false;
    return true;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( debug ) sb.p('_').p(_uid);
    sb.p(_name);
    sb.p('{');
    boolean field_sep=false;
    for( int i=0; i<nargs(); i++ ) {
      if( !debug && i==CTL_IDX && Util.eq(_args[CTL_IDX]," ctl") ) continue; // Do not print the Control
      if( !debug && i==MEM_IDX && Util.eq(_args[MEM_IDX]," mem") ) continue; // Do not print the memory
      if( !debug && i==DSP_IDX && Util.eq(_args[DSP_IDX],"^"   ) ) continue; // Do not print the ever-present display
      sb.p(_args[i]);
      if( arg(i) != Type.SCALAR )
        arg(i).str(sb.p(':'),dups,mem,debug);
      sb.p(" ");  field_sep=true;
    }
    if( field_sep ) sb.unchar();
    sb.p(" -> ");
    if( _ret != Type.SCALAR ) _ret.str(sb,dups,mem,debug);
    return sb.p('}');
  }

  private static TypeFunSig FREE=null;
  private TypeFunSig free( TypeFunSig ret ) { FREE=this; return ret; }
  public static TypeFunSig make( String[] args, TypeTuple formals, TypeTuple ret ) {
    TypeFunSig t1 = FREE == null ? new TypeFunSig() : FREE;
    FREE = null;
    TypeFunSig t2 = t1.init(args,formals,ret).hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeFunSig make( TypeTuple ret, Type[] ts ) { return make(func_names,TypeTuple.make_args(ts),ret); }
  public static TypeFunSig make( TypeTuple ret, TypeMemPtr disp, Type arg1 ) { return make(ret,Types.ts(disp,arg1)); }
  public static TypeFunSig make( TypeTuple ret, TypeMemPtr disp, Type arg1, Type arg2 ) { return make(ret,Types.ts(disp,arg1,arg2)); }
  public static TypeFunSig make( TypeTuple ret, TypeTuple formals ) { return make(func_names,formals,ret); }
  public TypeFunSig make_from_arg( int idx, Type arg ) { return make(_args,_formals.make_from_arg(idx,arg),_ret); }

  public static final String[] func_names = new String[]{" ctl", " mem", "^" , "arg3", "arg4", "arg5" }; // TODO: Extend as needed

  public static final TypeFunSig II_I = make(TypeTuple.make_ret(TypeInt.INT64),TypeTuple.INT64_INT64);
  static final TypeFunSig[] TYPES = new TypeFunSig[]{II_I};

  public int nargs() { return _formals._ts.length; }
  public Type arg(int idx) { return _formals._ts[idx]; }
  public Type display() { return arg(DSP_IDX); }

  @Override protected TypeFunSig xdual() { return new TypeFunSig().init(_args,_formals.dual(),_ret.dual()); }
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
    return make((TypeTuple)_ret.meet(tf._ret),(TypeTuple)_formals.meet(tf._formals));
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
