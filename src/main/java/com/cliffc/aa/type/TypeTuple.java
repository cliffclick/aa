package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;

import java.util.BitSet;

// Internal fixed-length non-recursive tuples.  Used for function arguments,
// and multi-arg results like IfNode and CallNode.  This is not the same as a
// no-named-field TypeStruct, and is not exposed at the language level.
public class TypeTuple<O extends TypeTuple<O>> extends Type<O> {
  public boolean _any;
  public Type[] _ts; // The fixed known types
  protected TypeTuple( byte type, boolean any, Type[] ts ) { super(type); init(type, any, ts);  }
  protected void init( byte type, boolean any, Type[] ts ) {
    super.init(type);
    _any = any;
    _ts = ts;
  }

  // If visit is null, children have had their hash already computed.
  // If visit is not null, children need to be recursively visited.
  @Override public int compute_hash( ) {
    int hash = TTUPLE+(_any?0:1);
    for( Type t : _ts ) hash += t.compute_hash();
    return hash;
  }
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
  @Override protected O free( O ret ) { FREE=this; return ret; }
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
  public  static final TypeTuple SCALAR2 = make(SCALAR, SCALAR);
          static final TypeTuple INT32   = make(TypeInt.INT32 );
  public  static final TypeTuple INT64   = make(TypeInt.INT64 );
  public  static final TypeTuple FLT64   = make(TypeFlt.FLT64 );
  public  static final TypeTuple STRPTR  = make(TypeMemPtr.STRPTR);
  public  static final TypeTuple OOP_OOP = make(TypeMemPtr.OOP0,TypeMemPtr.OOP0);
  public  static final TypeTuple INT64_INT64 = make(TypeInt.INT64,TypeInt.INT64);
  public  static final TypeTuple FLT64_FLT64 = make(TypeFlt.FLT64,TypeFlt.FLT64);
  private static final TypeTuple FLT64_INT64 = make(TypeFlt.FLT64,TypeInt.INT64);
  public  static final TypeTuple STR_STR     = make(TypeMemPtr.STRPTR,TypeMemPtr.STRPTR);
  
  public  static final TypeTuple IF_ANY  = make(XCTRL,XCTRL);
  public  static final TypeTuple IF_ALL  = make(CTRL ,CTRL );
  public  static final TypeTuple IF_TRUE = make(XCTRL,CTRL );
  public  static final TypeTuple IF_FALSE= make(CTRL ,XCTRL);

  // This is the starting state of the program; CTRL is active and memory is empty.
  public  static final TypeTuple START_STATE = make(CTRL, TypeMem.EMPTY_MEM);
  public  static final TypeTuple CALL  = make(CTRL, TypeMem.MEM, SCALAR);
  static final TypeTuple[] TYPES = new TypeTuple[]{XSCALARS,SCALAR0,SCALAR1,STRPTR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64, IF_ALL, IF_TRUE, IF_FALSE, OOP_OOP};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected O xdual() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return (O)new TypeTuple(TTUPLE, !_any, ts);
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    if( t._type != TTUPLE ) return ALL; // Tuples are internal types only, not user exposed
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

  @Override public boolean above_center() { return _any; }
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
  @Override public boolean must_nil() { return false; }
  @Override Type not_nil() { return this; }
  @Override public Type meet_nil() { return TypeNil.make(this); }

  // Return true if this is a function pointer (return type from EpilogNode)
  // 0 - Control for the function
  // 1 - Return type of the function as implemented
  // 2 - RPC (set of callers)
  // 3 - Classic TypeFunPtr, includes declared return type
  final boolean is_fun() {
    return _ts.length==5 &&
     (_ts[0]==CTRL || _ts[0]==XCTRL) &&
      _ts[1] instanceof TypeMem &&
      _ts[2].isa(SCALAR) &&
      _ts[3] instanceof TypeRPC &&
      //assert ts[4].is_con(); // Not always a constant F-P, e.g. Unresolved doing joins of F-P's
      _ts[4] instanceof TypeFunPtr;
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
  
}
