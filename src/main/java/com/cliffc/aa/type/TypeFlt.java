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
  private TypeFlt init(boolean any, boolean nil, boolean sub, int z, double con, BitsAlias aliases ) {
    super.init(any,nil,sub,aliases,BitsFun.EMPTY);
    _z=(byte)z;
    _con = con;
    return this;
  }

  @Override TypeFlt chk() {
    assert _z!=0 || !_any; // Constants are centerline, ignore "any", so "all" is canonical
    assert _aliases.test_recur(BitsAlias.FLTX);
    assert _fidxs==BitsFun.EMPTY;
    return super.chk();
  }

  static BitsAlias bits(boolean any) {
    return any ? BitsAlias.FLT.dual() : BitsAlias.FLT;
  }

  @Override protected TypeFlt copy() {
    TypeFlt tf = super.copy();
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
  
  @Override PENV _str0( PENV P ) {
    return _z==0
      ? P.p(_con).p(((float)_con)==_con ? "f" : "")
      : P.p(_strn()).p("flt").p(_z);
  }
  
  static TypeFlt valueOfFlt(String cid) {
    if( cid==null ) return null;
    return switch(cid) {
    case "flt64"  -> FLT64;
    case "flt32"  -> FLT32;
    case "nflt64" -> NFLT64;
    case "nflt32" -> NFLT32;
    default       -> null;
    };
  }
  static { new Pool(TFLT,new TypeFlt()); }
  public static TypeFlt make( boolean any, boolean nil, boolean sub, int z, double con ) {
    return make(any,nil,sub,z,con,bits(any));
  }
  public static TypeFlt make( boolean any, boolean nil, boolean sub, int z, double con, BitsAlias aliases ) {
    TypeFlt t1 = POOLS[TFLT].malloc();
    return t1.init(any,nil,sub,z,con,aliases).canonicalize().chk().hashcons_free();
  }
  @Override TypeFlt canonicalize() {
    if( _con!=0 ) {
      assert !_any && !_nil;
      if( !_sub ) { _z=(byte)log(_con); _con=0; } // constant plus zero is no longer a constant
    }
    return this;
  }

  public static TypeFlt con(double con) { return make(false,false,true,0,con); }

  public static final TypeFlt FLT64 = make(false,false,false,64,0);
  public static final TypeFlt FLT32 = make(false,false,false,32,0);
  public static final TypeFlt NFLT64= make(false,false,true ,64,0);
  public static final TypeFlt NFLT32= make(false,false,true ,32,0);
  public static final TypeFlt PI    = con(Math.PI);
  public static final TypeFlt HALF  = con(0.5);
  public static final TypeFlt ZERO  = con(0.0);
  public static final TypeFlt[] TYPES = new TypeFlt[]{FLT64,PI,FLT32,NFLT32,HALF};
  static void init1( HashMap<String,TypeNil> types ) {
    types.put("flt32",FLT32);
    types.put("flt64",FLT64);
    types.put("flt"  ,FLT64);
  }
  // Return a double from a TypeFlt constant; assert otherwise.
  @Override public double getd() { assert is_con(); return _con; }

  @Override protected TypeFlt xdual() {
    if( _z==0 ) return this;
    TypeFlt x = super.xdual();
    x._z = _z;
    x._con = 0;
    return x;
  }
  @Override protected TypeFlt xmeet( Type t ) {
    TypeFlt ti = (TypeFlt)t;
    TypeFlt rez = ymeet(ti);
    rez._con = 0;
    if( !rez._any ) {
      int lz0 =    _z==0 ? log(   _con) :    _z;
      int lz1 = ti._z==0 ? log(ti._con) : ti._z;
      if(    _z==0 && ti._any && (ti._nil || ti._sub) && lz0 <= lz1 ) return rez.free(this); // Keep a constant
      if( ti._z==0 &&    _any && (   _nil ||    _sub) && lz1 <= lz0 ) return rez.free(ti  ); // Keep a constant
      rez._z = (byte)(_any ? lz1 : (ti._any ? lz0 : Math.max(lz0,lz1)));
    } else {
      // Both are high, not constants.  Narrow size.
      rez._z = (byte)Math.min(_z,ti._z);
    }
    return rez.chk().hashcons_free();
  }
  static int log( double con ) { return ((double)(float)con)==con ? 32 : 64; }
  @Override boolean chk(BitsAlias aliases) { return aliases.test_recur(BitsAlias.FLTX); }


  @Override public TypeFlt widen() {
    if( !_nil && _sub ) return NFLT64;
    return FLT64;
  }
  @Override TypeNil widen_sub() {
    BitsAlias aliases = _aliases.above_center() ? _aliases.dual() : _aliases;
    return make(false,_nil,_sub,aliases,_fidxs);
  }
  @Override public boolean is_con() { return _z==0; }
  
  // Shallow wrap
  public TypeMemPtr wrap() {
    return TypeMemPtr.make(false,false,false,is_con(),BitsAlias.EMPTY,TypeStruct.make_prim(TypeFld.make_clz(TypeMemPtr.FLTPTR),TypeFld.make_prim(this))); // Wrapped primitive
  }
}
