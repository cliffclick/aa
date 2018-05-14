package com.cliffc.aa;

import com.cliffc.aa.util.SB;

import java.util.Arrays;

/** record/struct types; infinitely extended with an extra type (typically ANY or ALL) */
public class TypeTuple extends Type {
  public Type[] _ts;            // The fixed known types
  public Type _inf;             // Infinite extension type
  private int _hash;
  private TypeTuple( Type[] ts, Type inf ) { super(TTUPLE); init(ts,inf);  }
  private void init( Type[] ts, Type inf ) {
    _ts = ts;
    _inf = inf;
    int sum=TTUPLE+inf.hashCode();
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
    if( _ts.length != t._ts.length || _inf != t._inf) return false;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] ) return false;
    return true;
  }
  @Override public String toString() {
    SB sb = new SB().p("[");
    for( Type t : _ts ) sb.p(t.toString()).p(',');
    return sb.p(_inf.toString()).p("...]").toString();
  }
  
  private static TypeTuple FREE=null;
  private TypeTuple free( TypeTuple f ) { FREE=f; return this; }
  private static TypeTuple make( Type inf, boolean ignore, Type... ts ) {
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(ts,inf);
    else { FREE = null; t1.init(ts,inf); }
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  public static TypeTuple make( Type... ts ) { return make(TypeErr.ANY,1.0,ts); }
  public static TypeTuple make( Type inf, double ignore, Type... ts ) {
    int len = ts.length;
    while( len > 0 && ts[len-1] == inf ) len--;
    if( len < ts.length ) ts = Arrays.copyOf(ts,len);
    return make(inf,false, ts);
  }    

  public  static final TypeTuple  ANY    = make(); // Infinite list of Any
  public  static final TypeTuple  ALL    = (TypeTuple)make().dual(); // Infinite list of All
  public  static final TypeTuple  SCALAR = make(Type. SCALAR);
          static final TypeTuple  SCALAR2= make(Type. SCALAR, Type. SCALAR);
          static final TypeTuple XSCALAR1= make(Type.XSCALAR);
          static final TypeTuple XSCALAR2= make(Type.XSCALAR, Type.XSCALAR);
  public  static final TypeTuple INT32   = make(TypeInt.INT32 );
  public  static final TypeTuple INT64   = make(TypeInt.INT64 );
  public  static final TypeTuple FLT64   = make(TypeFlt.FLT64 );
  public  static final TypeTuple STR     = make(TypeStr.STR   );
  public  static final TypeTuple INT64_INT64 = make(TypeInt.INT64,TypeInt.INT64);
  public  static final TypeTuple FLT64_FLT64 = make(TypeFlt.FLT64,TypeFlt.FLT64);
  private static final TypeTuple FLT64_INT64 = make(TypeFlt.FLT64,TypeInt.INT64);
  public  static final TypeTuple IF_ANY  = ANY;
  public  static final TypeTuple IF_ALL  = make(Type.CONTROL,Type.CONTROL);
  public  static final TypeTuple IF_TRUE = make(TypeErr.ANY ,Type.CONTROL);
  public  static final TypeTuple IF_FALSE= make(Type.CONTROL             );
  static final TypeTuple[] TYPES = new TypeTuple[]{ANY,SCALAR,STR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64, IF_ALL, IF_TRUE, IF_FALSE};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeTuple xdual() {
    if( _ts.length==0 && _inf.dual()==_inf ) return this; // Self-symmetric
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeTuple(ts,_inf.dual());
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE: break;
    case TUNION:
    case TFLT:
    case TINT:
    case TSTR:
    case TFUN: return TypeErr.ALL;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    default: throw typerr(t);
    }
    // Length is longer of 2 tuples.  Shorter elements take the meet; longer
    // elements meet the shorter extension.
    TypeTuple tt = (TypeTuple)t;
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }

  // Meet 2 tuples, shorter is 'this'
  TypeTuple xmeet1(TypeTuple tmax) {
    Type[] ts = new Type[tmax._ts.length];
    // Meet of common elements
    for( int i=0; i<_ts.length; i++ )  ts[i] = _ts[i].meet(tmax._ts[i]);
    // Meet of elements only in the longer tuple
    for( int i=_ts.length; i<tmax._ts.length; i++ )
      ts[i] = _inf.meet(tmax._ts[i]);
    // Reduce common tail
    Type tail = _inf.meet(tmax._inf);
    int len = ts.length;
    while( len > 0 && ts[len-1] == tail ) len--;
    if( len < ts.length ) ts = Arrays.copyOf(ts,len);
    return make(tail,false, ts);
  }

  public Type at( int idx ) { return idx < _ts.length ? _ts[idx] : _inf; }
  
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
