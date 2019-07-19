package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;

import java.util.BitSet;

// Internal fixed-length non-recursive tuples.  Used for function arguments,
// and multi-arg results like IfNode and CallNode.  This is not the same as a
// no-named-field TypeStruct, and is not exposed at the language level.  With
// mixed tuple lengths, tuples are infinitely extended with ANY/ALL.
public class TypeTuple extends Type<TypeTuple> {
  private boolean _any;
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
    for( Type t : _ts ) hash += t._hash;
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
      int j = _ts.length-1;     // Find length of trailing equal parts
      Type last = _ts[j];       // Last type
      for( j--; j>0; j-- ) if( _ts[j] != last )  break;
      sb.p(_ts[0].str(dups));   // First type
      for( int i=1; i<=j; i++ ) // All types up to trailing equal parts
        sb.p(',').p(_ts[i].str(dups));
      if( j+1<_ts.length-1 )  sb.p("..."); // Abbreviate tail
      if( _ts.length> 1 ) sb.p(',').p(last);
    }
    sb.p(')');
    return sb.toString();
  }

  private static TypeTuple FREE=null;
  @Override protected TypeTuple free( TypeTuple ret ) { FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  static TypeTuple make0( boolean any, Type... ts ) {
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(TTUPLE, any, ts);
    else { FREE = null; t1.init(TTUPLE, any, ts); }
    assert t1._type==TTUPLE;
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeTuple make( Type... ts ) { return make0(false,ts); }
  // Arguments are infinitely-extended with ALL
  public static TypeTuple make_args( Type... ts ) { return make0(/*QQQfalse*/false,ts); }

  // Most primitive function call argument type lists are 0-based
          static final TypeTuple ALL_ARGS= make0(/*QQQfalse*/false); // Zero args and high
  private static final TypeTuple SCALAR0 = make_args();
  private static final TypeTuple SCALAR1 = make_args(SCALAR);
  public  static final TypeTuple SCALAR2 = make_args(SCALAR, SCALAR);
  private static final TypeTuple INT32   = make_args(TypeInt.INT32 );
  public  static final TypeTuple INT64   = make_args(TypeInt.INT64 );
  public  static final TypeTuple FLT64   = make_args(TypeFlt.FLT64 );
  public  static final TypeTuple STRPTR  = make_args(TypeMemPtr.STRPTR);
  public  static final TypeTuple OOP_OOP = make_args(TypeMemPtr.OOP0,TypeMemPtr.OOP0);
  public  static final TypeTuple INT64_INT64 = make_args(TypeInt.INT64,TypeInt.INT64);
  public  static final TypeTuple FLT64_FLT64 = make_args(TypeFlt.FLT64,TypeFlt.FLT64);
  private static final TypeTuple FLT64_INT64 = make_args(TypeFlt.FLT64,TypeInt.INT64);
  public  static final TypeTuple STR_STR     = make_args(TypeMemPtr.STRPTR,TypeMemPtr.STRPTR);

  public  static final TypeTuple IF_ANY  = make(XCTRL,XCTRL);
  public  static final TypeTuple IF_ALL  = make(CTRL ,CTRL );
  public  static final TypeTuple IF_TRUE = make(XCTRL,CTRL );
  public  static final TypeTuple IF_FALSE= make(CTRL ,XCTRL);

  // This is the starting state of the program; CTRL is active and memory is empty.
  public  static final TypeTuple START_STATE = make(CTRL, TypeMem.EMPTY_MEM);
  public  static final TypeTuple CALL  = make(CTRL, TypeMem.MEM, SCALAR);
  public  static final TypeTuple XCALL = CALL.dual();
  static final TypeTuple[] TYPES = new TypeTuple[]{SCALAR0,SCALAR1,STRPTR,INT32,INT64,FLT64,INT64_INT64,FLT64_FLT64,FLT64_INT64, IF_ALL, IF_TRUE, IF_FALSE, OOP_OOP};

  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @SuppressWarnings("unchecked")
  @Override protected TypeTuple xdual() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeTuple(TTUPLE, !_any, ts);
  }
  // Standard Meet.  Tuples have an infinite extent of 'ALL' for low, or 'ANY'
  // for high.  After the meet, the infinite tail is trimmed.
  @Override protected Type xmeet( Type t ) {
    if( t._type != TTUPLE ) return ALL; // Tuples are internal types only, not user exposed
    TypeTuple tt = (TypeTuple)t;
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }

  // Meet 2 tuples, shorter is 'this'.
  private TypeTuple xmeet1( TypeTuple tmax ) {
    // Short is high; short extended by ANY so tail is a copy of long.
    // Short is low ; short extended by ALL so tail is ALL so trimmed to short.
    int len = _any ? tmax._ts.length : _ts.length;
    // Meet of common elements
    Type[] ts = new Type[len];
    for( int i=0; i<_ts.length; i++ )  ts[i] = _ts[i].meet(tmax._ts[i]);
    // Elements only in the longer tuple.
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
  // 1 - Return memory type, as implemented
  // 2 - Return type of the function as implemented
  // 3 - RPC (set of callers)
  final boolean is_fun() {
    return _ts.length==4 &&
     (_ts[0]==CTRL || _ts[0]==XCTRL) &&
      _ts[1] instanceof TypeMem &&
      _ts[2].isa(SCALAR) &&
      _ts[3] instanceof TypeRPC;
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

  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.opto() state.
  @Override public TypeTuple startype() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].startype();
    return make0(!_any, ts);
  }
}
