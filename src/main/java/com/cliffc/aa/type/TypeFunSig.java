package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

// Function signatures: formal arguments (and return) used to type-check.  This
// is NOT any "code pointer" or "function index" or "fidx"; see TypeFunPtr.
public final class TypeFunSig extends Type<TypeFunSig> {
  // Formal 0 is the Display pointer.
  // Formal 1 is the Memory type, using TypeObj.ISUSED for ignored memory state.
  // Formals 2-N are the normal arguments.
  public String[] _args;
  public TypeTuple _formals;
  public Type _ret;

  private TypeFunSig(String[] args, TypeTuple formals, Type ret ) { super(TFUNSIG); init(args,formals,ret); }
  private void init (String[] args, TypeTuple formals, Type ret ) {
    assert args.length==formals.len();
    assert Util.eq(args[0]," mem") && formals.at(0) instanceof TypeMem;
    assert Util.eq(args[1],"^"   ) && formals.at(1).is_display_ptr();
    _args=args;
    _formals=formals;
    _ret=ret;
  }
  @Override int compute_hash() {
    assert _formals._hash != 0;
    int hash=TFUNSIG + _formals._hash + _ret._hash;
    for( int i=0; i<_args.length; i++ ) i+=_args.hashCode();
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
      if( !debug && i==0 && Util.eq(_args[i]," mem") ) continue; // Do not print the memory
      if( !debug && i==1 && Util.eq(_args[i],"^"   ) ) continue; // Do not print the ever-present display
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
  @Override protected TypeFunSig free( TypeFunSig ret ) { FREE=this; return ret; }
  public static TypeFunSig make( String[] args, TypeTuple formals, Type ret ) {
    assert args.length==formals.len();
    assert Util.eq(args[0]," mem") && formals._ts[0] instanceof TypeMem;
    assert Util.eq(args[1],"^"   ) && formals._ts[1].is_display_ptr();
    assert ret.isa(SCALAR) || ret instanceof TypeTuple;
    TypeFunSig t1 = FREE;
    if( t1 == null ) t1 = new TypeFunSig(args,formals,ret);
    else {   FREE = null;        t1.init(args,formals,ret); }
    TypeFunSig t2 = (TypeFunSig)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeFunSig make( Type ret, Type[] ts ) { return make(arg_names(ts.length),TypeTuple.make_args(ts),ret); }
  public static TypeFunSig make( Type ret, TypeMemPtr disp, Type arg1 ) { return make(ret,Types.ts(disp,arg1)); }
  public static TypeFunSig make( Type ret, TypeMemPtr disp, Type arg1, Type arg2 ) { return make(ret,Types.ts(disp,arg1,arg2)); }
  public static TypeFunSig make( TypeTuple formals, Type ret ) { return make(arg_names(formals.len()),formals,ret); }

  static String[] flds(String... fs) { return fs; }
  static final String[] ARGS_   = flds(" mem","^");            // Used for functions of 0 args
  static final String[] ARGS_X  = flds(" mem","^","x");        // Used for functions of 1 arg
  static final String[] ARGS_XY = flds(" mem","^","x","y");    // Used for functions of 2 args
  static final String[] ARGS_XYZ= flds(" mem","^","x","y","z");// Used for functions of 3 args
  static final String[][] ARGS = new String[][]{null,null,ARGS_,ARGS_X,ARGS_XY,ARGS_XYZ};
  public static String[] arg_names(int i) { return ARGS[i]; }

  public static final TypeFunSig II_I = make(TypeTuple.INT64_INT64,TypeInt.INT64);
  static final TypeFunSig[] TYPES = new TypeFunSig[]{II_I};

  public int nargs() { return _formals._ts.length; }
  public Type arg(int idx) { return _formals._ts[idx]; }
  public TypeMemPtr display() { return (TypeMemPtr)arg(0); }

  @Override protected TypeFunSig xdual() { return new TypeFunSig(_args,_formals.dual(),_ret.dual()); }
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
    return make((TypeTuple)_formals.meet(tf._formals),_ret.meet(tf._ret));
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
