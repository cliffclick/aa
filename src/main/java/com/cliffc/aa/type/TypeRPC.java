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
  static final TypeRPC[] TYPES = new TypeRPC[]{make(1),ALL_CALL};
  
  @Override protected TypeRPC xdual() { return new TypeRPC(_rpcs.dual()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TOOP:
    case TTUPLE: 
    case TFUNPTR:
    case TSTRUCT:
    case TFUN:
    case TFLT:
    case TINT:
    case TSTR:   return Type.SCALAR;
    case TRPC:   break;
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    default: throw typerr(t);   // All else should not happen
    }
    TypeRPC tf = (TypeRPC)t;
    return make(_rpcs.meet( tf._rpcs ));
  }
  
  public int rpc() { return _rpcs.getbit(); }
  public boolean test(int rpc) { return _rpcs.test(rpc); }
  @Override public boolean above_center() { return _rpcs.above_center(); }
  @Override public boolean may_be_con()   { return _rpcs.abit()>0; }
  @Override public boolean is_con()       { return _rpcs.abit()>0; }
}
