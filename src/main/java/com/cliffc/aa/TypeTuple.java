package com.cliffc.aa;

import com.cliffc.aa.util.SB;

import java.util.Arrays;

/** record/struct types; infinitely extended with either Any or All (so
 *  duck-like typing works); extra type fields are ignored.  */
public class TypeTuple extends Type {
  public boolean _all;          // Infinite extension via All
  public Type[] _ts;
  private int _hash;
  private TypeTuple( boolean all, Type[] ts ) { super(TTUPLE); init(all,ts);  }
  private void init( boolean all, Type[] ts ) {
    _all = all;
    _ts = ts;
    int sum=TTUPLE+(all?1:0);
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
    if( _ts.length != t._ts.length || _all != t._all) return false;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] ) return false;
    return true;
  }
  @Override public String toString() {
    SB sb = new SB().p("[");
    for( Type t : _ts ) sb.p(t.toString()).p(',');
    return sb.p(_all?"All":"Any").p("...]").toString();
  }
  
  private static TypeTuple FREE=null;
  private TypeTuple free( TypeTuple f ) { FREE=f; return this; }
  public static TypeTuple make( Type... ts ) { return make(false,ts); }
  public static TypeTuple make( boolean all, Type... ts ) {
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(all,ts);
    else { FREE = null; t1.init(all,ts); }
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  public  static final TypeTuple  ANY    = make(); // Infinite list of Any
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
  public  static final TypeTuple IF_ANY  = ANY;
  public  static final TypeTuple IF_ALL  = make(Type.CONTROL,Type.CONTROL);
  public  static final TypeTuple IF_TRUE = make(TypeErr.ANY ,Type.CONTROL);
  public  static final TypeTuple IF_FALSE= make(Type.CONTROL             );
  static final TypeTuple[] TYPES = new TypeTuple[]{ANY,SCALAR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64, IF_ALL, IF_TRUE, IF_FALSE};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Flipping the "_any" flag just flips the meaning
  // of the infinitely extended tail types (and not any of the explicitly
  // represented types).
  @Override protected TypeTuple xdual() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeTuple(!_all,ts);
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE: break;
    case TUNION:
    case TFLT:
    case TINT:
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
      ts[i] = (_all?TypeErr.ALL:TypeErr.ANY).meet(tmax._ts[i]);
    // Reduce common tail
    boolean all = _all || tmax._all;
    TypeErr tail = all?TypeErr.ALL:TypeErr.ANY;
    int len = ts.length;
    while( len > 0 && ts[len-1] == tail ) len--;
    if( len < ts.length ) ts = Arrays.copyOf(ts,len);
    return make(all, ts);
  }

  public Type at( int idx ) { return idx < _ts.length ? _ts[idx] : (_all?TypeErr.ALL:TypeErr.ANY); }
  
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
