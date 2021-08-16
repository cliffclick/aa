package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import static com.cliffc.aa.AA.*;

// Internal fixed-length non-recursive tuples.  Used for function arguments,
// and multi-arg results like IfNode and CallNode.  This is not the same as a
// no-named-field TypeStruct, and is not exposed at the language level.  With
// mixed tuple lengths, tuples are infinitely extended with ANY/ALL.
public class TypeTuple extends Type<TypeTuple> {
  boolean _any;
  public Type[] _ts; // The fixed known types
  protected TypeTuple init( boolean any, Type[] ts ) {
    super.init(TTUPLE,"");
    _any = any;
    _ts = ts;
    return this;
  }

  // If visit is null, children have had their hash already computed.
  // If visit is not null, children need to be recursively visited.
  private static int rot(int x, int k) { return (x<<k) | (x>>(32-k)); }
  @SuppressWarnings("fallthrough")
  @Override public int compute_hash( ) {
    int hash = TTUPLE+(_any?0:1);
    // Copied from http://burtleburtle.net/bob/c/lookup3.c
    int i,a,b,c;
    a = b = c = 0xdeadbeef + (_ts.length<<2) + hash;
    for( i=0; i+2<_ts.length; i+=3 ) {
      a += _ts[i  ]._hash;
      b += _ts[i+1]._hash;
      c += _ts[i+2]._hash;
      a -= c;  a ^= rot(c, 4);  c += b;
      b -= a;  b ^= rot(a, 6);  a += c;
      c -= b;  c ^= rot(b, 8);  b += a;
      a -= c;  a ^= rot(c,16);  c += b;
      b -= a;  b ^= rot(a,19);  a += c;
      c -= b;  c ^= rot(b, 4);  b += a;
    }
    switch(_ts.length-i) {
    case 3: c += _ts[i+2]._hash;
    case 2: b += _ts[i+1]._hash;
    case 1: a += _ts[i  ]._hash;
      c ^= b; c -= rot(b,14);
      a ^= c; a -= rot(c,11);
      b ^= a; b -= rot(a,25);
      c ^= b; c -= rot(b,16);
      a ^= c; a -= rot(c, 4);
      b ^= a; b -= rot(a,14);
      c ^= b; c -= rot(b,24);
    case 0:
      break;
    }
    return c;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeTuple) ) return false;
    TypeTuple t = (TypeTuple)o;
    return _any==t._any && _hash == t._hash && Types.eq(_ts,t._ts);
  }
  // Never part of a cycle so the normal equals works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( _any ) sb.p('~');
    sb.p('(');
    if( _ts!=null && _ts.length>0 ) { // No commas for zero-length
      int j = _ts.length-1;     // Find length of trailing equal parts
      Type last = _ts[j];       // Last type
      for( j--; j>0; j-- ) if( _ts[j] != last )  break;
      _ts[0].str(sb,dups,mem,debug);    // First type
      for( int i=1; i<=j+1; i++ ) // All types up to trailing equal parts
        _ts[i].str(sb.p(','),dups,mem,debug);
      if( j+2<_ts.length-1 )  sb.p("..."); // Abbreviate tail
      if( _ts.length> j+2 ) last.str(sb.p(','),dups,mem,debug);
    }
    return sb.p(')');
  }

  static { new Pool(TTUPLE,new TypeTuple()); }
  private static TypeTuple make( boolean any, Type[] ts ) {
    TypeTuple t1 = POOLS[TTUPLE].malloc();
    return t1.init(any,ts).hashcons_free();
  }

  public static TypeTuple make0( boolean any, Type[] ts ) { return make(any,Types.hash_cons(ts)); }
  public static TypeTuple make( Type[] ts ) { return make0(false,ts); }
  public static TypeTuple make( ) { return make0(false,Types.get(0)); }
  public static TypeTuple make( Type t0, Type t1 ) { return make0(false,Types.ts(t0,t1)); }
  public static TypeTuple make( Type t0, Type t1, Type t2 ) { return make0(false,Types.ts(t0,t1,t2)); }
  public static TypeTuple make( Type t0, Type t1, Type t2, Type t3 ) { return make0(false,Types.ts(t0,t1,t2,t3)); }
  public static TypeTuple make( Type t0, Type t1, Type t2, Type t3, Type t4 ) { return make0(false,Types.ts(t0,t1,t2,t3,t4)); }
  public static TypeTuple make( Type t0, Type t1, Type t2, Type t3, Type t4, Type t5 ) { return make0(false,Types.ts(t0,t1,t2,t3,t4,t5)); }

  // Make a Call args tuple from a Struct by adding Memory up front
  public static TypeTuple make(TypeStruct ts) {
    // TypeStruct includes a display/DSP_IDX, but what comes before
    Type[] ts2 = Types.get(ts.len()+DSP_IDX);
    ts2[CTL_IDX] = Type.CTRL;
    ts2[MEM_IDX] = TypeMem.ALLMEM;
    //for( int i=0; i<ts.len(); i++ )
    //  ts2[DSP_IDX+i] = ts.at(i);
    //return make(ts2);
    throw unimpl();
  }
  public static TypeTuple make_args(Type[] ts) {
    assert ts[MEM_IDX] instanceof TypeMem && ts[DSP_IDX].is_display_ptr();
    return make(ts);
  }

  public static TypeTuple make_args(                       ) { return make(Type.CTRL,TypeMem.ALLMEM,Type.ALL ); }
  public static TypeTuple make_args(Type t2                ) { return make(Type.CTRL,TypeMem.ALLMEM,Type.ALL,t2); }
  public static TypeTuple make_args(Type t2,Type t3        ) { return make(Type.CTRL,TypeMem.ALLMEM,Type.ALL,t2,t3); }
  public static TypeTuple make_ret(Type trez) { return make(Type.CTRL,TypeMem.ANYMEM,trez); }


  public  static final TypeTuple IF_ALL  = make(CTRL ,CTRL );
  public  static final TypeTuple IF_ANY  = IF_ALL.dual();
  public  static final TypeTuple IF_TRUE = make(XCTRL,CTRL );
  public  static final TypeTuple IF_FALSE= make(CTRL ,XCTRL);

  // This is the starting state of the program; CTRL is active and memory is empty.
  public  static final TypeTuple START_STATE = make(CTRL, TypeMem.EMPTY);
  public  static final TypeTuple  RET = make(CTRL, TypeMem.ALLMEM, ALL); // Type of RetNodes
  public  static final TypeTuple CALLE= make(CTRL, TypeMem.ALLMEM, ALL); // Type of CallEpiNodes
  public  static final TypeTuple TEST0= make(CTRL, TypeMem.MEM  , TypeFunPtr.GENERIC_FUNPTR, SCALAR); // Call with 1 arg
  public  static final TypeTuple TEST1= make(CTRL, TypeMem.EMPTY, TypeFunPtr.GENERIC_FUNPTR, SCALAR); // Call with 1 arg
  // Arguments
  public  static final TypeTuple NO_ARGS    = make_args();
  public  static final TypeTuple INT64      = make_args(TypeInt.INT64); // {int->flt}
  public  static final TypeTuple FLT64      = make_args(TypeFlt.FLT64); // {flt->flt}
  public  static final TypeTuple STRPTR     = make_args(TypeMemPtr.STRPTR);
  public  static final TypeTuple INT64_INT64= make_args(TypeInt.INT64,TypeInt.INT64); // {int int->int }
  public  static final TypeTuple FLT64_FLT64= make_args(TypeFlt.FLT64,TypeFlt.FLT64); // {flt flt->flt }
  public  static final TypeTuple OOP_OOP    = make_args(TypeMemPtr.ISUSED0,TypeMemPtr.ISUSED0);
  public  static final TypeTuple SCALAR1    = make_args(SCALAR);

  //
  static final TypeTuple[] TYPES = new TypeTuple[]{
    CALLE,START_STATE,IF_ALL, IF_TRUE, IF_FALSE, TEST0, TEST1,
    NO_ARGS, INT64, FLT64, STRPTR, INT64_INT64, FLT64_FLT64, OOP_OOP
  };

  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeTuple xdual() {
    Type[] ts = Types.get(_ts.length);
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    ts = Types.hash_cons(ts);
    return new TypeTuple().init(!_any, ts);
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
  @Override public Type meet_nil(Type t) { throw unimpl(); }

  public TypeTuple sharptr( TypeMem mem ) {
    Type[] ts = Types.clone(_ts);
    for( int i=0; i<ts.length; i++ )
      ts[i] = mem.sharptr(ts[i]);
    return make0(_any,ts);
  }
  @Override public Type simple_ptr() {
    Type[] ts = Types.clone(_ts);
    for( int i=0; i<ts.length; i++ )
      ts[i] = ts[i].simple_ptr();
    return make0(_any,ts);
  }

  @Override public TypeTuple widen() {
    Type[] ts = Types.get(_ts.length);
    for( int i=0; i<ts.length; i++ )
      ts[i] = _ts[i].widen();
    return make(ts);
  }

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t instanceof TypeTuple ) {
      TypeTuple tt = (TypeTuple)t;
      if( tt._ts.length != _ts.length ) return 99;
      byte x;
      for( int i=0; i<_ts.length; i++ )
        if( (x=_ts[i].isBitShape(tt._ts[i])) != 0 )
          return x;
      return 0;
    }
    return 99;
  }
}
