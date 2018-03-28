package com.cliffc.aa;

import java.util.Arrays;

public class TypeTuple extends Type {
  public Type[] _ts;
  private int _hash;
  TypeTuple( Type[] ts ) { super(TTUPLE); init(ts);  }
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
  
  static public final TypeTuple EMPTY   = make(new Type[0]);
  static public final TypeTuple  SCALAR = make(Type.SCALAR);
  static public final TypeTuple XSCALAR1= make(Type.XSCALAR);
  static public final TypeTuple XSCALAR2= make(Type.XSCALAR, Type.XSCALAR);
  static public final TypeTuple INT32   = make(TypeInt.INT32 );
  static public final TypeTuple INT64   = make(TypeInt.INT64 );
  static public final TypeTuple FLT64   = make(TypeFlt.FLT64 );
  static public final TypeTuple INT64_INT64 = make(TypeInt.INT64,TypeInt.INT64);
  static public final TypeTuple FLT64_FLT64 = make(TypeFlt.FLT64,TypeFlt.FLT64);
  static public final TypeTuple FLT64_INT64 = make(TypeFlt.FLT64,TypeInt.INT64);
  static public final TypeTuple[] TYPES = new TypeTuple[]{SCALAR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64};
  
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
    TypeTuple tt = (TypeTuple)t;
    // The length of Tuples is a constant, and a mismatch on length is a
    // complete miss: the result falls to Bottom.
    if( _ts.length != tt._ts.length ) return Type.ALL;
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].meet(tt._ts[i]);
    return make(ts);
  }
  // Per-element meet.  Return the results as the caller may have more
  // processing.
  Type[] meet_per_elem(Type t) {
    Type[] ts = new Type[_ts.length];
    boolean equals=true;
    for( int i=0; i<_ts.length; i++ ) {
      ts[i] = _ts[i].meet(t);
      if( ts[i]!=_ts[i] ) equals=false;
    }
    return equals?_ts:ts;  // Return 'this' if no change
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
    for( int i=0; i<_ts.length; i++ ) if( _ts[i].canBeConst() ) return true;
    return false;
  }
}
