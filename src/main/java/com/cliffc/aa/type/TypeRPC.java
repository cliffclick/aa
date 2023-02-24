package com.cliffc.aa.type;

import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// Return-Program-Counters, or Continuation constants
public class TypeRPC extends TypeNil<TypeRPC> {
  private BitsRPC _rpcs;         //

  private TypeRPC init( boolean any, boolean nil, boolean sub, BitsRPC rpcs ) {
    super.init(any,nil,sub, BitsAlias.EMPTY, BitsFun.EMPTY);
    assert _any==rpcs.above_center() || rpcs==BitsRPC.EMPTY;
    _rpcs = rpcs;
    return this;
  }

  @Override protected TypeRPC copy() {
    TypeRPC tr = super.copy();
    tr._rpcs = _rpcs;
    return tr;
  }

  @Override public long static_hash( ) { return ((TRPC + (long)_rpcs._hash)<<1)|1; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !super.equals(o) || !(o instanceof TypeRPC rpc) ) return false;
    return _rpcs==rpc._rpcs;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _any ) sb.p('~');
    return _str_nil(_rpcs.str(sb.p("#")));
  }

  static TypeRPC valueOf(Parse P, String cid, boolean any) {
    P.require('#');
    var rpcs = P.bits(BitsRPC.EMPTY);
    assert any==rpcs.above_center() || rpcs.is_empty();
    TypeRPC rpc = malloc(any, rpcs.test(0),true, rpcs.clear(0)).val_nil(P).hashcons_free();
    if( cid!=null ) P._dups.put(cid,rpc);
    return rpc;
  }

  static { new Pool(TRPC,new TypeRPC()); }
  public static TypeRPC malloc( boolean any, boolean nil, boolean sub, BitsRPC rpcs ) {
    return POOLS[TRPC].<TypeRPC>malloc().init(any,nil,sub,rpcs);
  }
  public static TypeRPC make( boolean any, boolean nil, boolean sub, BitsRPC rpcs ) { return malloc(any,nil,sub,rpcs).hashcons_free(); }

  public static TypeRPC make( int rpc ) { return make(false,false,true,BitsRPC.make0(rpc)); }
  public static final TypeRPC ALL_CALL = make(false,false,true,BitsRPC.NALL);
  private static final TypeRPC RPC1 = make(BitsRPC.new_rpc(BitsRPC.ALLX));
  private static final TypeRPC EMPTY = make(false,false,true,BitsRPC.EMPTY);
  static final TypeRPC[] TYPES = new TypeRPC[]{RPC1,ALL_CALL,EMPTY};

  @Override protected TypeRPC xdual() {
    TypeRPC x = super.xdual();
    x._rpcs = _rpcs.dual();
    return x;
  }
  @Override protected TypeRPC xmeet( Type t ) {
    TypeRPC rpc = (TypeRPC)t;
    TypeRPC rez = ymeet(rpc);
    rez._rpcs = _rpcs.meet( rpc._rpcs );
    return rez.hashcons_free();
  }

  public int rpc() { return _rpcs.getbit(); }
  public boolean test(int rpc) { return _rpcs.test(rpc); }
  // RPCs represent *classes* of return pointers and are thus never constants.
  // TODO: This is weak, since call-sites are only rarely cloned so typically a
  // RPC refers to the single call-site - but we can only strengthen this is we
  // declare a call-site to be uncloneable.
  // nil is a constant.
  @Override public boolean is_con() { return false; }
}
