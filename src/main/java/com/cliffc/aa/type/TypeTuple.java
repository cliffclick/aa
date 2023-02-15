package com.cliffc.aa.type;

import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

// Internal fixed-length non-recursive tuples.  Used for function arguments,
// and multi-arg results like IfNode and CallNode.  This is not the same as a
// no-named-field TypeStruct, and is not exposed at the language level.  With
// mixed tuple lengths, tuples are infinitely extended with ANY/ALL.
public class TypeTuple extends Type<TypeTuple> {
  boolean _any;
  public Type[] _ts; // The fixed known types
  protected TypeTuple init( boolean any, Type[] ts ) {
    super.init();
    _any = any;
    _ts = ts;
    return this;
  }

  // If visit is null, children have had their hash already computed.
  // If visit is not null, children need to be recursively visited.
  @Override public long static_hash( ) { return (_any?0:2047) ^ ((long) _ts.length <<2); }
  @Override long compute_hash() {
    Util.add_hash(super.static_hash() ^ static_hash());
    for( Type t : _ts )
      Util.add_hash(t._hash);
    return Util.get_hash();
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeTuple t) ) return false;
    return _any==t._any && _hash == t._hash && _ts==t._ts;
  }
  // Never part of a cycle so the normal equals works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override public void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    for( Type t : _ts )
      if( t!=null )
        t._str_dups(visit,dups,ucnt);
  }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _any ) sb.p('~');
    sb.p('{');
    if( _ts!=null && _ts.length>0 ) { // No commas for zero-length
      int j = _ts.length-1;     // Find length of trailing equal parts
      Type last = _ts[j];       // Last type
      for( j--; j>0; j-- ) if( _ts[j] != last )  break;
      _ts[0]._str(visit,dups, sb, debug, indent ); // First type
      for( int i=1; i<=j+1; i++ ) // All types up to trailing equal parts
        _ts[i]._str(visit,dups, sb.p(','), debug, indent );
      if( j+2<_ts.length-1 )  sb.p("..."); // Abbreviate tail
      if( _ts.length> j+2 ) last._str(visit,dups, sb.p(','), debug, indent);
    }
    return sb.p('}');
  }

  static TypeTuple valueOf(Parse P, String cid, boolean any) {
    P.require('{');
    Type[] ts = Types.get(10);
    int i=0;
    while(true) {
      ts[i++] = Cyclic.install(P.type(null,false,-2),P._dups);
      if( !P.peek(',') ) break;
    }
    Type[] ts0 = Types.get(i);
    System.arraycopy(ts,0,ts0,0,i);
    Types.free(ts);
    TypeTuple tt = make0(any,ts0);
    if( cid!=null ) P._dups.put(cid,tt);
    P.require('}');
    return tt;
  }

  static { new Pool(TTUPLE,new TypeTuple()); }
  private static TypeTuple make( boolean any, Type[] ts ) {
    TypeTuple t1 = POOLS[TTUPLE].malloc();
    return t1.init(any,ts).hashcons_free();
  }

  public static TypeTuple make0( boolean any, Type[] ts ) { return make(any,Types.hash_cons(ts)); }
  public static TypeTuple make( Type[] ts ) { return make0(false,ts); }
  public static TypeTuple make( ) { return make0(false,Types.get(0)); }
  public static TypeTuple make( Type t0 ) { return make0(false,Types.ts(t0)); }
  public static TypeTuple make( Type t0, Type t1 ) { return make0(false,Types.ts(t0,t1)); }
  public static TypeTuple make( Type t0, Type t1, Type t2 ) { return make0(false,Types.ts(t0,t1,t2)); }
  public static TypeTuple make( Type t0, Type t1, Type t2, Type t3 ) { return make0(false,Types.ts(t0,t1,t2,t3)); }
  public static TypeTuple make( Type t0, Type t1, Type t2, Type t3, Type t4 ) { return make0(false,Types.ts(t0,t1,t2,t3,t4)); }
  public static TypeTuple make( Type t0, Type t1, Type t2, Type t3, Type t4, Type t5 ) { return make0(false,Types.ts(t0,t1,t2,t3,t4,t5)); }

  public TypeTuple make_from( int idx, Type t ) {
    if( _ts[idx]==t ) return this;
    Type[] ts = Types.clone(_ts);
    ts[idx] = t;
    return make0(_any,ts);
  }

  public  static final TypeTuple IF_ALL  = make(CTRL ,CTRL );
  public  static final TypeTuple IF_ANY  = IF_ALL.dual();
  public  static final TypeTuple IF_TRUE = make(XCTRL,CTRL );
  public  static final TypeTuple IF_FALSE= make(CTRL ,XCTRL);

  // This is the starting state of the program; CTRL is active and memory is empty.
  public  static final TypeTuple  RET = make(CTRL, TypeMem.ALLMEM, ALL); // Type of RetNodes
  public  static final TypeTuple CALLE= make(CTRL, TypeMem.ALLMEM, ALL); // Type of CallEpiNodes
  public  static final TypeTuple ROOT = make(CTRL, TypeMem.ALLMEM, TypeRPC.ALL_CALL, TypeNil.SCALAR); // Type of Root  
  public  static final TypeTuple TEST0= make(CTRL, TypeMem.ALLMEM, TypeFunPtr.GENERIC_FUNPTR, TypeNil.SCALAR); // Call with 1 arg
  public  static final TypeTuple TEST1= make(CTRL, TypeMem.ANYMEM, TypeFunPtr.GENERIC_FUNPTR, TypeNil.SCALAR); // Call with 1 arg
  // Arguments
  public  static final TypeTuple INT64      = make(CTRL, TypeMem.ALLMEM, TypeInt.INT64); // { int -> }
  public  static final TypeTuple FLT64      = make(CTRL, TypeMem.ALLMEM, TypeFlt.FLT64); // { flt -> }
  public  static final TypeTuple INT64_INT64= make(CTRL, TypeMem.ALLMEM, TypeInt.INT64,TypeInt. INT64); // { int  int -> }
  public  static final TypeTuple INT64_NFLT64=make(CTRL, TypeMem.ALLMEM, TypeInt.INT64,TypeFlt.NFLT64); // { int nflt -> }
  public  static final TypeTuple FLT64_FLT64= make(CTRL, TypeMem.ALLMEM, TypeFlt.FLT64,TypeFlt. FLT64); // { flt  flt -> }
  public  static final TypeTuple FLT64_INT64= make(CTRL, TypeMem.ALLMEM, TypeFlt.FLT64,TypeInt. INT64); // { flt  int -> }
  public  static final TypeTuple STR        = make(CTRL, TypeMem.ALLMEM, TypeMemPtr.STRPTR);            // { str -> }
  public  static final TypeTuple OOP_OOP    = make(CTRL, TypeMem.ALLMEM, TypeMemPtr.ISUSED0,TypeMemPtr.ISUSED0);

  //
  static final TypeTuple[] TYPES = new TypeTuple[]{
    CALLE,IF_ALL, IF_TRUE, IF_FALSE, TEST0, TEST1,
    INT64, FLT64, INT64_INT64, FLT64_FLT64, OOP_OOP
  };

  // The length of Tuples is a constant, and so is its own dual.  Otherwise,
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeTuple xdual() {
    Type[] ts = Types.get(_ts.length);
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    ts = Types.hash_cons(ts);
    return POOLS[TTUPLE].<TypeTuple>malloc().init(!_any, ts);
  }
  // Standard Meet.  Tuples have an infinite extent of 'ALL' for low, or 'ANY'
  // for high.  After the meet, the infinite tail is trimmed.
  @Override protected Type xmeet( Type t ) {
    TypeTuple tt = (TypeTuple)t;
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }

  // Meet 2 tuples, shorter is 'this'.
  private TypeTuple xmeet1( TypeTuple tmax ) {
    // Short is high; short extended by ANY so tail is a copy of long.
    // Short is low ; short extended by ALL so tail is ALL so trimmed to short.
    int len = _any ? tmax._ts.length : _ts.length;
    // Meet of common elements
    Type[] ts = Types.get(len);
    for( int i=0; i<_ts.length; i++ )  ts[i] = _ts[i].meet(tmax._ts[i]);
    // Elements only in the longer tuple.
    if( len > _ts.length ) System.arraycopy(tmax._ts, _ts.length, ts, _ts.length, len - _ts.length);
    return make0(_any&tmax._any,ts);
  }

  public Type at( int idx ) { return _ts[idx]; } // Must be in-size
  public int len() { return _ts.length; }

  // Same as the original, with one field changed
  public TypeTuple set( int idx, Type t ) {
    Type[] ts = Types.clone(_ts);
    ts[idx]=t;
    return make(ts);
  }


  @Override public boolean above_center() { return _any; }
  // True if all internals is_con
  @Override public boolean is_con() {
    for( Type _t : _ts ) if( !_t.is_con() ) return false;
    return true;
  }
  @Override public TypeTuple sharptr2( TypeMem mem ) {
    Type[] ts = Types.clone(_ts);
    for( int i=0; i<ts.length; i++ )
      ts[i] = ts[i].sharptr2(mem);
    return make0(_any,ts);
  }
  @Override public Type simple_ptr() {
    Type[] ts = Types.clone(_ts);
    for( int i=0; i<ts.length; i++ )
      ts[i] = ts[i].simple_ptr();
    return make0(_any,ts);
  }

}
