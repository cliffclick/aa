package com.cliffc.aa.type;

import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

import java.util.BitSet;

// Return-Program-Counters, or Continuation constants
public class TypeRPC extends Type<TypeRPC> {
  public Bits _rpcs;            // 

  private TypeRPC( Bits rpcs ) { super(TRPC); init(rpcs); }
  private void init( Bits rpcs ) { _rpcs = rpcs; }
  @Override public int hashCode( ) { return TRPC + _rpcs.hashCode();  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeRPC) ) return false;
    TypeRPC tf = (TypeRPC)o;
    return _rpcs==tf._rpcs;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    SB sb = new SB().p("#");
    return _rpcs.toString(sb).toString();
  }
  
  private static TypeRPC FREE=null;
  @Override protected TypeRPC free( TypeRPC ret ) { FREE=this; return ret; }
  public static TypeRPC make( int rpc ) { return make(Bits.make(rpc)); }
  public static TypeRPC make( Bits rpcs ) {
    TypeRPC t1 = FREE;
    if( t1 == null ) t1 = new TypeRPC(rpcs);
    else { FREE = null; t1.init(rpcs); }
    TypeRPC t2 = (TypeRPC)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static final TypeRPC ALL_CALL = make(Bits.FULL);
  public static final TypeRPC RPC1 = make(1);
  static final TypeRPC[] TYPES = new TypeRPC[]{RPC1,ALL_CALL};
  
  @Override protected TypeRPC xdual() { return new TypeRPC(_rpcs.dual()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TRPC:   break;
    case TFUNPTR:
    case TMEMPTR:
    case TFLT:
    case TINT:   return cross_nil(t);
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    case TTUPLE: 
    case TFUN:
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
  @Override public boolean above_center() { return _rpcs.above_center(); }
  @Override public boolean may_be_con()   { return _rpcs.is_con() || _rpcs.above_center(); }
  @Override public boolean is_con()       { return _rpcs.is_con(); }
  @Override public boolean must_nil() { return _rpcs.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _rpcs.may_nil(); }
  @Override Type not_nil() {
    // Below center, return this; above center remove nil choice
    return above_center() && _rpcs.test(0) ? make(_rpcs.clear(0)) : this;
  }
  @Override public Type meet_nil() {
    if( _rpcs.test(0) )      // Already has a nil?
      return _rpcs.above_center() ? TypeNil.NIL : this;
    return make(_rpcs.meet(Bits.make(0)));
  }
}
