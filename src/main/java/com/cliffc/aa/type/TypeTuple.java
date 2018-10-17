package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;

import java.util.Arrays;
import java.util.BitSet;

/** record/struct types; infinitely extended with an extra type (typically ANY or ALL) */
public class TypeTuple<P extends TypeTuple<P>> extends TypeOop<P> {
  public Type[] _ts;      // The fixed known types
  public Type _inf;       // Infinite extension type
  private int _hash;
  protected TypeTuple( byte type, boolean any, Type[] ts, Type inf ) { super(type,any); init(type, any, ts,inf);  }
  protected void init( byte type, boolean any, Type[] ts, Type inf ) {
    super.init(type,any);
    _ts = ts;
    _inf = inf;
    int sum=super.hashCode()+inf.hashCode();
    for( Type t : ts ) sum += t.hashCode();
    _hash=sum;
  }
  
  @Override public int hashCode( ) { return _hash;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeTuple && eq((TypeTuple)o);
  }    
  boolean eq( TypeTuple t ) {
    if( _hash != t._hash ) return false;
    if( !super.eq(t) || _ts.length != t._ts.length || _inf != t._inf )
      return false;
    if( _ts == t._ts ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] ) return false;
    return true;
  }
  @Override String str( BitSet dups) {
    SB sb = new SB();
    if( _any ) sb.p('~');
    sb.p('(');
    if( _ts.length>0 ) {        // No commas for zero-length
      sb.p(_ts[0].str(dups));
      for( int i=1; i<_ts.length; i++ )
        sb.p(',').p(_ts[i].str(dups));
    }
    if( _inf!=ALL ) sb.p(',').p(_inf.str(dups)).p("...");
    sb.p(')');
    return sb.toString();
  }

  private static TypeTuple FREE=null;
  @Override protected TypeTuple free( TypeTuple ret ) { FREE=this; return ret; }
  private static TypeTuple make0( Type inf, boolean any, Type... ts ) {
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(TTUPLE, any, ts,inf);
    else { FREE = null; t1.init(TTUPLE, any, ts,inf); }
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeTuple make( Type inf, float ignore, Type... ts ) {
    assert !inf.is_con();
    int len = ts.length;
    while( len > 0 && ts[len-1] == inf ) len--;
    if( len < ts.length ) ts = Arrays.copyOf(ts,len);
    TypeTuple tt = make0(inf, inf.above_center(), ts);
    assert !tt.is_fun();    // Use funptr class for this
    return tt;
  }
  public static TypeTuple make     ( Type... ts ) { return make(ANY,1.0f,ts); }
  public static TypeTuple make_all ( Type... ts ) { return make(ALL,1.0f,ts); }
  public static TypeTuple make_args( Type... ts ) { return make(SCALAR,1.0f,ts); }

          static final TypeTuple XSCALARS= make(XSCALAR,1.0f);
  public  static final TypeTuple SCALAR0 = make_args();
          static final TypeTuple SCALAR1 = make_args(SCALAR);
          static final TypeTuple SCALAR2 = make_args(SCALAR, SCALAR);
  public  static final TypeTuple INT32   = make_args(TypeInt.INT32 );
  public  static final TypeTuple INT64   = make_args(TypeInt.INT64 );
  public  static final TypeTuple FLT64   = make_args(TypeFlt.FLT64 );
  public  static final TypeTuple STR     = make_args(TypeStr.STR   );
  public  static final TypeTuple OOP_OOP = make_args(TypeNil.OOP,TypeNil.OOP);
  public  static final TypeTuple INT64_INT64 = make_args(TypeInt.INT64,TypeInt.INT64);
  public  static final TypeTuple FLT64_FLT64 = make_args(TypeFlt.FLT64,TypeFlt.FLT64);
  private static final TypeTuple FLT64_INT64 = make_args(TypeFlt.FLT64,TypeInt.INT64);
  public  static final TypeTuple IF_ANY  = make_all(XCTRL,XCTRL);
  public  static final TypeTuple IF_ALL  = make_all(CTRL ,CTRL );
  public  static final TypeTuple IF_TRUE = make_all(XCTRL,CTRL );
  public  static final TypeTuple IF_FALSE= make_all(CTRL ,XCTRL);
  static final TypeTuple[] TYPES = new TypeTuple[]{XSCALARS,SCALAR0,SCALAR1,STR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64, IF_ALL, IF_TRUE, IF_FALSE, OOP_OOP};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected P xdual() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return (P)new TypeTuple(TTUPLE, !_any, ts,_inf.dual());
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE: break;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TFUN:
    case TRPC:   return SCALAR;
    case TSTR:   return OOP;
    case TOOP:
    case TSTRUCT:
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    // Length is longer of 2 tuples.  Shorter elements take the meet; longer
    // elements meet the shorter extension.
    TypeTuple tt = (TypeTuple)t;
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }

  // Meet 2 tuples, shorter is 'this'
  private TypeTuple xmeet1( TypeTuple tmax ) {
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
    return make0(tail,_any && tmax._any,ts);
  }

  public Type at( int idx ) { return idx < _ts.length ? _ts[idx] : _inf; }

  // True if all internals may_be_con
  @Override public boolean may_be_con() {
    for( Type _t : _ts ) if( !_t.may_be_con() ) return false;
    return _inf.may_be_con();
  }
  // True if all internals is_con
  @Override public boolean is_con() {
    for( Type _t : _ts ) if( !_t.is_con() ) return false;
    return true;
  }

  // Return true if this is a function pointer (return type from EpilogNode)
  // 0 - Control for the function
  // 1 - Return type of the function as implemented
  // 2 - RPC (set of callers)
  // 3 - Classic TypeFunPtr, includes declared return type
  final boolean is_fun() {
    return _ts.length==4 &&
     (_ts[0]==CTRL || _ts[0]==XCTRL) &&
      _ts[2] instanceof TypeRPC &&
      //assert ts[3].is_con(); // Not always a constant F-P, e.g. Unresolved doing joins of F-P's
      _ts[3] instanceof TypeFunPtr;
  }

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t instanceof TypeName ) return t.isBitShape(this);
    if( t instanceof TypeNil ) return isBitShape(((TypeNil)t)._t);
    if( t instanceof TypeStruct ) return 99; // Not allowed to upcast a tuple to a struct
    if( t instanceof TypeTuple ) {
      TypeTuple tt = (TypeTuple)t;
      if( tt._ts.length != _ts.length ) return 99;
      byte x;
      for( int i=0; i<_ts.length; i++ )
        if( (x=_ts[i].isBitShape(tt._ts[i])) != 0 )
          return x;
    }
    
    throw AA.unimpl();
  }
  
  // Make a (posssibly cyclic & infinite) named type.  Prevent the infinite
  // unrolling of names by not allowing a named-type with depth >= D from
  // holding (recursively) the head of a named-type cycle.  We need to cap the
  // unroll, to prevent loops/recursion from infinitely unrolling.
  @Override TypeTuple<P> make_recur(TypeName tn, int d, BitSet bs ) {
    boolean eq = _inf.make_recur(tn,d,bs)==_inf;
    for( Type t : _ts )
      eq = eq && t.make_recur(tn,d,bs)==t;
    if( eq ) return this;
    // Build a depth-limited version of the same struct
    throw AA.unimpl();
  }
  // Return an error message, if any exists
  @Override public String errMsg() {
    String s;
    for( Type t : _ts )
      if( (s=t.errMsg()) != null )
        return s;
    return null;
  }
}
