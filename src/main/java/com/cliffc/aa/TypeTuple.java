package com.cliffc.aa;

import java.util.Arrays;

public class TypeTuple extends Type {
  public Type[] _ts;
  private int _hash;
  private TypeTuple( Type[] ts ) { super(TTUPLE); init(ts);  }
  private void init(Type[] ts) {
    _ts = ts;
    int sum=TTUPLE;
    for( Type t : ts ) sum += t.hashCode();
    _hash=sum;
  }
  
  @Override public int hashCode( ) { return _hash;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeTuple) ) return false;
    TypeTuple t = (TypeTuple)o;
    if( _hash != t._hash ) return false;
    if( _ts == t._ts ) return true;
    if( _ts.length != t._ts.length ) return false;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] ) return false;
    return true;
  }
  @Override public String toString() { return Arrays.toString(_ts); }
  
  private static TypeTuple FREE=null;
  private TypeTuple free( TypeTuple f ) { FREE=f; return this; }
  public static TypeTuple make( Type... ts ) {
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(ts);
    else { FREE = null; t1.init(ts); }
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

          static final TypeTuple  EMPTY  = make();
          static final TypeTuple  SCALAR = make(Type. SCALAR);
          static final TypeTuple  SCALAR2= make(Type. SCALAR, Type. SCALAR);
          static final TypeTuple XSCALAR1= make(Type.XSCALAR);
          static final TypeTuple XSCALAR2= make(Type.XSCALAR, Type.XSCALAR);
  public  static final TypeTuple INT32   = make(TypeInt.INT32 );
  public  static final TypeTuple INT64   = make(TypeInt.INT64 );
          static final TypeTuple FLT64   = make(TypeFlt.FLT64 );
          static final TypeTuple INT64_INT64 = make(TypeInt.INT64,TypeInt.INT64);
          static final TypeTuple FLT64_FLT64 = make(TypeFlt.FLT64,TypeFlt.FLT64);
  private static final TypeTuple FLT64_INT64 = make(TypeFlt.FLT64,TypeInt.INT64);
  public  static final TypeTuple IF_CTRL = make(Type.CONTROL,Type.CONTROL);
  static final TypeTuple[] TYPES = new TypeTuple[]{SCALAR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64,IF_CTRL};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.
  @Override protected TypeTuple xdual() {
    boolean self=true;
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) {
      ts[i] = _ts[i].dual();
      if( ts[i] != _ts[i] ) self=false; // Not a self-dual
    }
    return self ? this : new TypeTuple(ts);
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE: break;
    case TFLT:
    case TINT:
    case TFUN: return Type.ALL;
    default: throw typerr(t);
    }
    // Length is longer of 2 tuples.
    // Shorter elements take the meet; longer elements just copy.
    TypeTuple tt = (TypeTuple)t;
    int min = Math.min(_ts.length,tt._ts.length);
    int max = Math.max(_ts.length,tt._ts.length);
    Type[] ts = new Type[max];
    for( int i=0; i<min; i++ ) ts[i] = _ts[i].meet(tt._ts[i]);
    if( min < max ) {
      Type[] tx = max==_ts.length ? _ts : tt._ts;
      for( int i=min; i<max; i++ )  ts[i] = tx[i];
    }
    return make(ts);
  }
  boolean has_tuple() {
    for( Type t : _ts ) if( t._type==Type.TTUPLE ) return true;
    return false;
  }
  @Override public TypeTuple ret() {
    throw AA.unimpl();
    //Type[] ts = new Type[_ts.length];
    //for( int i=0; i<_ts.length; i++ )
    //  ts[i] = ((TypeFun)_ts[i])._ret;
    //return new TypeTuple(ts);
  }
  // True if any internals canBeConst
  @Override protected boolean canBeConst() {
    for( Type _t : _ts ) if( _t.canBeConst() ) return true;
    return false;
  }
  // True if all internals is_con
  @Override public boolean is_con() {
    for( Type _t : _ts ) if( !_t.is_con() ) return false;
    return true;
  }
}
