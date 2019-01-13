package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;

import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Consumer;

/** Internal fixed-length non-recursive tuples.  Used for function arguments,
 *  and multi-arg results like IfNode and CallNode. */
public class TypeTuple<P extends TypeTuple<P>> extends TypeOop<P> {
  public Type[] _ts;     // The fixed known types
  private int _hash;     // Hash pre-computed to avoid large computes duing interning
  protected TypeTuple( byte type, boolean any, Type[] ts ) { super(type,any); init(type, any, ts);  }
  protected void init( byte type, boolean any, Type[] ts ) {
    super.init(type,any);
    _ts = ts;
    int sum=super.hashCode();
    for( Type t : ts ) sum += t.hashCode();
    _hash=sum;
  }
  
  @Override public int hashCode( ) { return _hash;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeTuple) ) return false;
    TypeTuple t = (TypeTuple)o;
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return false;
    if( _ts == t._ts ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] ) return false;
    return true;
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeTuple) ) return false;
    TypeTuple t = (TypeTuple)o;
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return false;
    if( _ts == t._ts ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] && !_ts[i].cycle_equals(t._ts[i]) ) return false;
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
    sb.p(')');
    return sb.toString();
  }

  private static TypeTuple FREE=null;
  @Override protected P free( P ret ) { FREE=this; return ret; }
  static TypeTuple make0( boolean any, Type... ts ) {
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(TTUPLE, any, ts);
    else { FREE = null; t1.init(TTUPLE, any, ts); }
    assert t1._type==TTUPLE;
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeTuple make( Type... ts ) {
    TypeTuple tt = make0(false,ts);
    assert !tt.is_fun();
    return tt;
  }

          static final TypeTuple XSCALARS= make0(true);
          static final TypeTuple SCALAR0 = make();
          static final TypeTuple SCALAR1 = make(SCALAR);
          static final TypeTuple SCALAR2 = make(SCALAR, SCALAR);
          static final TypeTuple INT32   = make(TypeInt.INT32 );
  public  static final TypeTuple INT64   = make(TypeInt.INT64 );
  public  static final TypeTuple FLT64   = make(TypeFlt.FLT64 );
  public  static final TypeTuple STR     = make(TypeStr.STR   );
  public  static final TypeTuple OOP_OOP = make(TypeNil.OOP,TypeNil.OOP);
  public  static final TypeTuple INT64_INT64 = make(TypeInt.INT64,TypeInt.INT64);
  public  static final TypeTuple FLT64_FLT64 = make(TypeFlt.FLT64,TypeFlt.FLT64);
  private static final TypeTuple FLT64_INT64 = make(TypeFlt.FLT64,TypeInt.INT64);
  public  static final TypeTuple STR_STR     = make(TypeStr.STR  ,TypeStr.STR  );
  
  public  static final TypeTuple IF_ANY  = make(XCTRL,XCTRL);
  public  static final TypeTuple IF_ALL  = make(CTRL ,CTRL );
  public  static final TypeTuple IF_TRUE = make(XCTRL,CTRL );
  public  static final TypeTuple IF_FALSE= make(CTRL ,XCTRL);
  static final TypeTuple[] TYPES = new TypeTuple[]{XSCALARS,SCALAR0,SCALAR1,STR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64, IF_ALL, IF_TRUE, IF_FALSE, OOP_OOP};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected P xdual() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return (P)new TypeTuple(TTUPLE, !_any, ts);
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE: break;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TFUN:
    case TRPC:   return t.must_nil() ? SCALAR : NSCALR;
    case TSTR:   return OOP;
    case TOOP:
    case TSTRUCT:
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    TypeTuple tt = (TypeTuple)t;
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }

  // Meet 2 tuples, shorter is 'this'
  private TypeTuple xmeet1( TypeTuple tmax ) {
    int len = _any ? tmax._ts.length : _ts.length;
    // Meet of common elements
    Type[] ts = new Type[len];
    for( int i=0; i<_ts.length; i++ )  ts[i] = _ts[i].meet(tmax._ts[i]);
    // Elements only in the longer tuple
    for( int i=_ts.length; i<len; i++ )
      ts[i] = tmax._ts[i];
    return make0(_any&tmax._any,ts);
  }

  public Type at( int idx ) { return _ts[idx]; } // Must be in-size

  // True if all internals may_be_con
  @Override public boolean may_be_con() {
    for( Type _t : _ts ) if( !_t.may_be_con() ) return false;
    return true;
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
  
  // Make a (possibly cyclic & infinite) named type.  Prevent the infinite
  // unrolling of names by not allowing a named-type with depth >= D from
  // holding (recursively) the head of a named-type cycle.  We need to cap the
  // unroll, to prevent loops/recursion from infinitely unrolling.
  @Override TypeTuple<P> make_recur(TypeName tn, int d, BitSet bs ) {
    throw AA.unimpl();
  }

  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { for( Type t : _ts) c.accept(t); }
  @Override boolean contains( Type t, BitSet bs ) {
    if( bs==null ) bs=new BitSet();
    for( Type t2 : _ts) if( t2==t || t2.contains(t,bs) ) return true;
    return false;
  }
  @Override int depth( BitSet bs ) {
    if( bs==null ) bs=new BitSet();
    int max=0;
    for( Type t : _ts) max = Math.max(max,t.depth(bs));
    return max+1;
  }
  @Override Type replace( Type old, Type nnn, HashMap<TypeStruct,TypeStruct> MEETS ) {
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
