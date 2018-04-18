package com.cliffc.aa;

public class TypeFun extends Type {
  public TypeTuple _ts;         // Arg types
  public Type _ret;             // return types
  private TypeFun( TypeTuple ts, Type ret ) { super(TFUN); init(ts,ret); }
  private void init(TypeTuple ts, Type ret ) { _ts = ts; _ret = ret; }
  @Override public int hashCode( ) { return TFUN + _ts.hashCode() + _ret.hashCode();  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFun) ) return false;
    TypeFun tf = (TypeFun)o;
    return _ts==tf._ts && _ret==tf._ret;
  }
  @Override public String toString() { return "{"+_ts+"->"+_ret+"}"; }
  private static TypeFun FREE=null;
  private TypeFun free( TypeFun f ) { FREE=f; return this; }
  public static TypeFun make( TypeTuple ts, Type ret ) {
    TypeFun t1 = FREE;
    if( t1 == null ) t1 = new TypeFun(ts,ret);
    else { FREE = null; t1.init(ts,ret); }
    TypeFun t2 = (TypeFun)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  public static TypeFun any( int nargs ) {
    switch( nargs ) {
    case 0: return SCR0;
    case 1: return SCR1;
    case 2: return SCR2;
    default: throw AA.unimpl();
    }
  }

  static public final TypeFun SCR0 = make(TypeTuple.EMPTY  ,Type.SCALAR);
  static public final TypeFun SCR1 = make(TypeTuple.SCALAR ,Type.SCALAR);
  static public final TypeFun SCR2 = make(TypeTuple.SCALAR2,Type.SCALAR);
  static public final TypeFun FLT64 = make(TypeTuple.FLT64,TypeFlt.FLT64); // [flt]->flt
  static public final TypeFun INT64 = make(TypeTuple.INT64,TypeInt.INT64); // [int]->int
  static public final TypeFun FLT64_FLT64 = make(TypeTuple.FLT64_FLT64,TypeFlt.FLT64); // [flt,flt]->flt
  static public final TypeFun INT64_INT64 = make(TypeTuple.INT64_INT64,TypeInt.INT64); // [int,int]->int
  static final TypeFun[] TYPES = new TypeFun[]{FLT64,INT64,FLT64_FLT64,INT64_INT64};
  
  @Override protected TypeFun xdual() { return new TypeFun((TypeTuple)_ts.dual(),_ret.dual()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TCONTROL:
    case TTUPLE:           return ALL;
    case TFLT:  case TINT: return Type.SCALAR;
    case TFUN:             break;
    default: throw typerr(t);   // All else should not happen
    }
    TypeFun tf = (TypeFun)t;
    Type targs = _ts.meet(tf._ts);
    if( !(targs instanceof TypeTuple) ) return Type.SCALAR;
    Type ret = _ret.join(tf._ret); // Notice JOIN, Functions are contravariant
    // Make a new signature
    return make((TypeTuple)targs,ret);
  }
  
  @Override public Type ret() { return _ret; }

  @Override protected boolean canBeConst() { return true; }
  boolean is_lossy() { return true; } // A few conversions are not lossy
}
