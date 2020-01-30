package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// Internal fixed-length non-recursive tuples.  Used for function arguments,
// and multi-arg results like IfNode and CallNode.  This is not the same as a
// no-named-field TypeStruct, and is not exposed at the language level.  With
// mixed tuple lengths, tuples are infinitely extended with ANY/ALL.
public class TypeTuple extends Type<TypeTuple> {
  boolean _any;
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
    return _any==t._any && _hash == t._hash && TypeAry.eq(_ts,t._ts);
  }
  // Never part of a cycle so the normal equals works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  String open_parens() { return "("; }
  String clos_parens() { return ")"; }
  @Override String str( VBitSet dups) {
    SB sb = new SB();
    if( _any ) sb.p('~');
    sb.p(open_parens());
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
    sb.p(clos_parens());
    return sb.toString();
  }

  private static TypeTuple FREE=null;
  @Override protected TypeTuple free( TypeTuple ret ) { FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  static TypeTuple make0( boolean any, Type[] ts ) {
    ts = TypeAry.hash_cons(ts);
    TypeTuple t1 = FREE;
    if( t1 == null ) t1 = new TypeTuple(TTUPLE, any, ts);
    else { FREE = null; t1.init(TTUPLE, any, ts); }
    assert t1._type==TTUPLE;
    TypeTuple t2 = (TypeTuple)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeTuple make( Type[] ts ) { return make0(false,ts); }
  public static TypeTuple make( ) { Type[] ts = TypeAry.get(0);  return make0(false,ts); }
  public static TypeTuple make( Type t0 ) { Type[] ts = TypeAry.get(1);  ts[0]=t0;  return make0(false,ts); }
  public static TypeTuple make( Type t0, Type t1 ) { Type[] ts = TypeAry.get(2);  ts[0]=t0; ts[1]=t1; return make0(false,ts); }
  public static TypeTuple make( Type t0, Type t1, Type t2 ) { Type[] ts = TypeAry.get(3); ts[0]=t0; ts[1]=t1; ts[2]=t2; return make0(false,ts); }
  public static TypeTuple make( Type t0, Type t1, Type t2, Type t3 ) { Type[] ts = TypeAry.get(4); ts[0]=t0; ts[1]=t1; ts[2]=t2; ts[3]=t3; return make0(false,ts); }
  public  static final TypeTuple IF_ANY  = make(XCTRL,XCTRL);
  public  static final TypeTuple IF_ALL  = make(CTRL ,CTRL );
  public  static final TypeTuple IF_TRUE = make(XCTRL,CTRL );
  public  static final TypeTuple IF_FALSE= make(CTRL ,XCTRL);

  // This is the starting state of the program; CTRL is active and memory is empty.
  public  static final TypeTuple START_STATE = make(CTRL, TypeMem.EMPTY);
  public  static final TypeTuple CALL  = make(CTRL, TypeMem.FULL, SCALAR);
  public  static final TypeTuple XCALL = CALL.dual();
  public  static final TypeTuple CALLE = make(CTRL, TypeMem.FULL, SCALAR, TypeMem.FULL);
  static final TypeTuple[] TYPES = new TypeTuple[]{CALL,CALLE,START_STATE,IF_ALL, IF_TRUE, IF_FALSE};

  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @SuppressWarnings("unchecked")
  @Override protected TypeTuple xdual() {
    Type[] ts = TypeAry.get(_ts.length);
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    ts = TypeAry.hash_cons(ts);
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
    Type[] ts = TypeAry.get(len);
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
  @Override public Type meet_nil() { throw AA.unimpl(); }

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
    Type[] ts = TypeAry.get(_ts.length);
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].startype();
    return make0(!_any, ts);
  }
}
