package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// Return-Program-Counters, or Continuation constants
public class TypeRPC extends Type<TypeRPC> {
  private BitsRPC _rpcs;         //

  private TypeRPC init( BitsRPC rpcs ) { super.init(""); _rpcs = rpcs; return this; }
  @Override public int compute_hash( ) { return ((TRPC + _rpcs._hash)<<1)|1; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeRPC) ) return false;
    TypeRPC tf = (TypeRPC)o;
    return _rpcs==tf._rpcs;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    return _rpcs.str(sb.p("#"));
  }

  static { new Pool(TRPC,new TypeRPC()); }
  public static TypeRPC make( BitsRPC rpcs ) {
    return POOLS[TRPC].<TypeRPC>malloc().init(rpcs).hashcons_free();
  }

  public static TypeRPC make( int rpc ) { return make(BitsRPC.make0(rpc)); }
  public static final TypeRPC ALL_CALL = make(BitsRPC.FULL);
  private static final TypeRPC RPC1 = make(BitsRPC.new_rpc(BitsRPC.ALL));
  private static final TypeRPC EMPTY = make(BitsRPC.EMPTY);
  static final TypeRPC[] TYPES = new TypeRPC[]{RPC1,ALL_CALL,EMPTY};

  @Override protected TypeRPC xdual() {
    return _rpcs==BitsRPC.EMPTY ? this : POOLS[TRPC].<TypeRPC>malloc().init(_rpcs.dual());
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TRPC:   break;
    case TFUNPTR:
    case TMEMPTR:
    case TFLT:
    case TINT:   return cross_nil(t);
    case TFUNSIG:
    case TTUPLE:
    case TARY:
    case TLIVE:
    case TOBJ:
    case TSTR:
    case TSTRUCT:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeRPC tf = (TypeRPC)t;
    return make(_rpcs.meet( tf._rpcs ));
  }

  public int rpc() { return _rpcs.getbit(); }
  public boolean test(int rpc) { return _rpcs.test(rpc); }
  @Override public Type widen() { return ALL_CALL; }
  @Override public boolean above_center() { return _rpcs.above_center(); }
  // RPCs represent *classes* of return pointers and are thus never constants.
  // TODO: This is weak, since call-sites are only rarely cloned so typically a
  // RPC refers to the single call-site - but we can only strengthen this is we
  // declare a call-site to be uncloneable.
  // nil is a constant.
  @Override public boolean may_be_con()   { return may_nil(); }
  @Override public boolean is_con()       { return _rpcs.abit()==0; } // only nil
  @Override public boolean must_nil() { return _rpcs.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _rpcs.may_nil(); }
  @Override Type not_nil() {
    BitsRPC bits = _rpcs.not_nil();
    return bits==_rpcs ? this : make(bits);
  }
  @Override public Type meet_nil(Type nil) {
    // See testLattice15.
    if( nil==XNIL )
      return _rpcs.test(0) ? (_rpcs.above_center() ? XNIL : SCALAR) : NSCALR;
    if( _rpcs.above_center() ) return make(BitsRPC.NIL);   
    BitsRPC rpcs = _rpcs.above_center() ? _rpcs.dual() : _rpcs;
    return make(rpcs.set(0));
  }
}
