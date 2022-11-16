package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.HashMap;

public class TypeFlt extends TypeNil<TypeFlt> {
  // If z==0, then _con has the constant, and the bitsize comes from that.
  // Constant int 0 has zero bits then.
  // If z!=0, then _con is zero and unused; z represents the range.
  // Bit ranges are 32,64
  // _any dictates high or low
  public  byte _z;        // bitsiZe, one of: 32,64
  private double _con;      // constant
  private TypeFlt init(boolean any, boolean nil, boolean sub, int z, double con ) {
    assert con==0 ^ z==0;
    super.init(any,nil,sub);
    _z=(byte)z;
    _con = con;
    return this;
  }
  @Override protected TypeFlt _copy() {
    TypeFlt tf = super._copy();
    tf._z = _z;
    tf._con = _con;
    return tf;
  }
  // Hash does not depend on other types
  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_z,(int)_con); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFlt t2) ) return false;
    return super.equals(o) && _z==t2._z && _con==t2._con;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _z==0 )      return ((float)_con)==_con ? sb.p((float)_con).p('f') : sb.p(_con);
    return _strn(sb).p("flt").p(_z);
  }

  static TypeFlt valueOfFlt(String cid) {
    if( cid==null ) return null;
    return switch(cid) {
    case "flt64"  -> FLT64;
    case "flt32"  -> FLT32;
    case "nflt32" -> NFLT32;
    default       -> null;
    };
  }
  static { new Pool(TFLT,new TypeFlt()); }
  public static TypeFlt make( boolean any, boolean nil, boolean sub, int z, double con ) {
    assert con==0 ^ z==0;
    if( con!=0 ) {
      assert !any && !nil;
      if( !sub ) { z=log(con); con=0; } // constant plus zero is no longer a constant
    }
    TypeFlt t1 = POOLS[TFLT].malloc();
    return t1.init(any,nil,sub,z,con).hashcons_free();
  }
  @Override TypeFlt make_from( boolean any, boolean nil, boolean sub ) {
    nil &= sub;
    return any == _any && nil == _nil && sub == _sub ? this : make(any,nil,sub,_z,_con);
  }

  public static TypeFlt con(double con) { return make(false,false,true,0,con); }

  public static final TypeFlt FLT64 = make(false,false,false,64,0);
  public static final TypeFlt FLT32 = make(false,false,false,32,0);
  public static final TypeFlt NFLT32= make(false,false,true ,32,0);
  public static final TypeFlt PI    = con(Math.PI);
  public static final TypeFlt HALF  = con(0.5);
  public static final TypeFlt[] TYPES = new TypeFlt[]{FLT64,PI,FLT32,NFLT32,HALF};
  static void init1( HashMap<String,Type> types ) {
    types.put("flt32",FLT32);
    types.put("flt64",FLT64);
    types.put("flt"  ,FLT64);
  }
  // Return a double from a TypeFlt constant; assert otherwise.
  @Override public double getd() { assert is_con(); return _con; }
  //@Override public long   getl() { assert is_con() && ((long)_con)==_con; return (long)_con; }

  @Override protected TypeFlt xdual() {
    boolean xor = _nil == _sub;
    return _z==0 ? this : POOLS[TFLT].<TypeFlt>malloc().init(!_any,_nil^xor,_sub^xor,_z,0);
  }
  @Override protected TypeFlt xmeet( Type t ) {
    TypeFlt ti = (TypeFlt)t;
    boolean any = _any & ti._any;
    boolean nil = _nil & ti._nil;
    boolean sub = _sub & ti._sub;
    
    if( !any ) {
      int lz0 =    _z==0 ? log(   _con) :    _z;
      int lz1 = ti._z==0 ? log(ti._con) : ti._z;
      if(    _z==0 && ti._any && (ti._nil || ti._sub) && lz0 <= lz1 ) return this; // Keep a constant
      if( ti._z==0 &&    _any && (   _nil ||    _sub) && lz1 <= lz0 ) return ti  ; // Keep a constant
      int nz = _any ? lz1 : (ti._any ? lz0 : Math.max(lz0,lz1));
      return make(any,nil,sub,nz,0);
    }
    // Both are high, not constants.  Narrow size.
    return make(any,nil,sub,Math.min(_z,ti._z),0);
  }
  static int log( double con ) { return ((double)(float)con)==con ? 32 : 64; }

  @Override public TypeFlt widen() { return FLT64; }
  @Override public boolean is_con() { return _z==0; }
}
