package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;

import java.util.Arrays;

/** record/struct types; infinitely extended with an extra type (typically ANY or ALL) */
public class TypeTuple extends Type {
  public Type[] _ts;      // The fixed known types
  public Type _inf;       // Infinite extension type
  boolean _nil;           // Tuple itself can be null (unrelated to the fields)
  private int _hash;
  private TypeTuple( Type[] ts, Type inf, boolean nil ) { super(TTUPLE); init(ts,inf,nil);  }
  private void init( Type[] ts, Type inf, boolean nil ) {
    _ts = ts;
    _inf = inf;
    _nil = nil;
    int sum=TTUPLE+inf.hashCode()+(_nil?0:1);
    for( Type t : ts ) sum += t.hashCode();
    _hash=sum;
  }
  
  @Override public int hashCode( ) { return _hash;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeTuple) ) return false;
    TypeTuple t = (TypeTuple)o;
    if( _hash != t._hash ) return false;
    if( _ts.length != t._ts.length || _inf != t._inf || _nil != t._nil )
      return false;
    if( _ts == t._ts ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] ) return false;
    return true;
  }
  @Override public String toString() {
    SB sb = new SB().p('[');
    for( Type t : _ts ) sb.p(t.toString()).p(',');
    if( _inf!=TypeErr.ALL ) sb.p(_inf.toString()).p("...");
    sb.p(']');
    if( _nil ) sb.p(above_center() ? "+?" : "?");
    return sb.toString();
  }

  private static TypeTuple FREE=null;
  private TypeTuple free( TypeTuple f ) { FREE=f; return this; }
  private static TypeTuple make0( Type inf, boolean nil, Type... ts ) {
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(ts,inf,nil);
    else { FREE = null; t1.init(ts,inf,nil); }
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  public static TypeTuple make    ( Type... ts ) { return make(TypeErr.ANY,false,ts); }
  public static TypeTuple make_all( Type... ts ) { return make(TypeErr.ALL,false,ts); }
  public static TypeTuple make( Type inf, boolean nil, Type... ts ) {
    int len = ts.length;
    while( len > 0 && ts[len-1] == inf ) len--;
    if( len < ts.length ) ts = Arrays.copyOf(ts,len);
    return make0(inf, nil, ts);
  }
  public static TypeTuple make_fun_ptr( TypeFun fun ) {
    TypeTuple t = make_all(Type.CTRL,TypeErr.ALL, TypeRPC.ALL_CALL, fun);
    assert t.is_fun_ptr();
    return t;
  }

  public  static final TypeTuple  ANY    = make(); // Infinite list of Any
  public  static final TypeTuple  ALL    = (TypeTuple)make().dual(); // Infinite list of All
  public  static final TypeTuple  ALL0   = make(TypeErr.ALL,true);
  public  static final TypeTuple  SCALAR0= make(Type.XSCALAR,false);
  public  static final TypeTuple  SCALAR1= make(Type.XSCALAR,false,Type. SCALAR);
          static final TypeTuple  SCALAR2= make(Type.XSCALAR,false,Type. SCALAR, Type. SCALAR);
  public  static final TypeTuple  SCALARS= make(Type. SCALAR,false);
  public  static final TypeTuple INT32   = make(Type.XSCALAR,false,TypeInt.INT32 );
  public  static final TypeTuple INT64   = make(Type.XSCALAR,false,TypeInt.INT64 );
  public  static final TypeTuple FLT64   = make(Type.XSCALAR,false,TypeFlt.FLT64 );
  public  static final TypeTuple STR     = make(Type.XSCALAR,false,TypeStr.STR   );
  public  static final TypeTuple INT64_INT64 = make(Type.XSCALAR,false,TypeInt.INT64,TypeInt.INT64);
  public  static final TypeTuple FLT64_FLT64 = make(Type.XSCALAR,false,TypeFlt.FLT64,TypeFlt.FLT64);
  private static final TypeTuple FLT64_INT64 = make(Type.XSCALAR,false,TypeFlt.FLT64,TypeInt.INT64);
  public  static final TypeTuple IF_ANY  = make_all(Type.XCTRL,Type.XCTRL);
  public  static final TypeTuple IF_ALL  = make_all(Type.CTRL ,Type.CTRL );
  public  static final TypeTuple IF_TRUE = make_all(Type.XCTRL,Type.CTRL );
  public  static final TypeTuple IF_FALSE= make_all(Type.CTRL ,Type.XCTRL);
  public  static final TypeTuple FUNPTR2 = make_fun_ptr(TypeFun.any(2,-1));
  public  static final TypeTuple GENERIC_FUN = make_fun_ptr(TypeFun.make_generic());
  public  static final TypeTuple OOP_OOP = make(Type.XSCALAR,false,TypeOop.OOP0,TypeOop.OOP0);
  static final TypeTuple[] TYPES = new TypeTuple[]{ANY,SCALAR1,STR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64, IF_ALL, IF_TRUE, IF_FALSE, FUNPTR2, OOP_OOP};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeTuple xdual() {
    boolean sym = _inf.dual()==_inf;
    if( _ts.length==0 && sym ) return this; // Self-symmetric
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) {
      ts[i] = _ts[i].dual();
      sym &= ts[i]==_ts[i];     // All elements self-symetric?
    }
    return sym ? this : new TypeTuple(ts,_inf.dual(),_nil);
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE: break;
    case TNAME:
    case TUNION:
    case TSTRUCT: return t.xmeet(this); // Let TypeStruct decide
    case TRPC:
    case TFUN:   return Type.SCALAR;
    case TSTR:
    case TFLT:
    case TINT:
      //if(   may_be_null() ) return t.meet(TypeInt.NULL);
      //if( t.may_be_null() ) return   meet_null();
      //return t._type==TFLT||t._type==TINT ? SCALAR : OOP0;
      throw AA.unimpl();
    case TERROR: return ((TypeErr)t)._all ? t : this;
    default: throw typerr(t);
    }
    // Length is longer of 2 tuples.  Shorter elements take the meet; longer
    // elements meet the shorter extension.
    TypeTuple tt = (TypeTuple)t;
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }

  // Meet 2 tuples, shorter is 'this'
  private TypeTuple xmeet1(TypeTuple tmax) {
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
    // If both are high and have nil choice, then nil choice.
    // If either is low and requires nil, then require nil.
    boolean nil = (above_center() && _nil && tmax._nil) ||
      (!     above_center() &&      _nil) ||
      (!tmax.above_center() && tmax._nil);
    return make0(tail,nil, ts);
  }

  public Type at( int idx ) { return idx < _ts.length ? _ts[idx] : _inf; }

  Type meet_null() { return above_center() && _nil ? TypeInt.NULL : ALL0; }
  
  boolean has_union_or_tuple() {
    for( Type t : _ts ) if( t._type==Type.TUNION || t._type==Type.TTUPLE || t._type==Type.TSTRUCT ) return true;
    return false;
  }
  @Override public boolean above_center() { return _inf.above_center(); }
  // True if all internals canBeConst
  @Override public boolean canBeConst() {
    if( above_center() && _nil ) return true; // can be nil
    for( Type _t : _ts ) if( !_t.canBeConst() ) return false;
    return _inf.canBeConst();
  }
  // True if all internals is_con
  @Override public boolean is_con() {
    for( Type _t : _ts ) if( !_t.is_con() ) return false;
    return _inf.is_con() && !_nil;
  }

  // Return true if this is a function pointer (return type from EpilogNode)
  // 0 - Control for the function
  // 1 - Return type of the function as implemented
  // 2 - RPC (set of callers)
  // 3 - Classic TypeFun, includes declared return type
  @Override public boolean is_fun_ptr() {
    return _ts.length==4 &&
     (_ts[0]==Type.CTRL || _ts[0]==Type.XCTRL|| _ts[0] instanceof TypeErr) &&
      _ts[2] instanceof TypeRPC &&
      _ts[3] instanceof TypeFun;
  }
  // Return true if this is a forward-ref function pointer (return type from EpilogNode)
  @Override public boolean is_forward_ref() {
    return is_fun_ptr() && ((TypeFun)_ts[3]).is_forward_ref();
  }
  public TypeFun get_fun() { assert is_fun_ptr(); return (TypeFun)_ts[3]; }
  // Return an error message, if any exists
  @Override public String errMsg() {
    String s;
    for( Type t : _ts )
      if( (s=t.errMsg()) != null )
        return s;
    return null;
  }
}
