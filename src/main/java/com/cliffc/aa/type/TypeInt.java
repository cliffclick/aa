package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.HashMap;

import static com.cliffc.aa.AA.unimpl;

public class TypeInt extends TypeNil<TypeInt> {
  // If z==0, then _con has the constant, and the bitsize comes from that.
  // Constant int 0 has zero bits then.
  // If z!=0, then _con is zero and unused; z represents the range.
  // Bit ranges are 1,8,16,32,64
  // _any dictates high or low
  public  byte _z;        // bitsiZe, one of: 1,8,16,32,64
  private long _con;      // constant
  private TypeInt init(boolean any, boolean nil, boolean sub, int z, long con ) {
    assert con==0 ^ z==0;
    super.init(any,nil,sub);
    _z=(byte)z;
    _con = con;
    return this;
  }

  @Override protected TypeInt _copy() {
    TypeInt ti = super._copy();
    ti._z = _z;
    ti._con = _con;
    return ti;
  }
  // Hash does not depend on other types
  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_z,(int)_con); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeInt t2) ) return false;
    return super.equals(o) && _z==t2._z && _con==t2._con;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _z==0 )
      return sb.p(_con);
    return _strn(sb).p("int").p(_z);
  }

  static Type valueOfInt(String cid) {
    return switch(cid) {
    case  "int64" ->  INT64;
    case  "int8"  ->  INT8 ;
    case  "int1"  -> BOOL;
    case "nint8"  -> NINT8 ;
    default       -> null;
    };
  }
  static { new Pool(TINT,new TypeInt()); }
  public static TypeInt make( boolean any, boolean nil, boolean sub, int z, long con ) {
    assert con==0 ^ z==0;
    // Canonicalize
    if( con!=0 ) {
      assert !any && !nil;
      if( !sub ) { z=log(con); con=0; } // constant plus zero is no longer a constant
    }
    TypeInt t1 = POOLS[TINT].malloc();
    return t1.init(any,nil,sub,z,con).hashcons_free();
  }
  @Override TypeInt make_from( boolean any, boolean nil, boolean sub ) { return make(any,nil,sub,_z,_con); }

  public static TypeInt con(long con) { assert con!=0; return make(false,false,true,0,con); }

  public  static final TypeInt NINT64= make(false,false, true,64,0);
  public  static final TypeInt INT64 = make(false,false,false,64,0);
  public  static final TypeInt INT32 = make(false,false,false,32,0);
  public  static final TypeInt INT16 = make(false,false,false,16,0);
  public  static final TypeInt INT8  = make(false,false,false, 8,0);
  public  static final TypeInt NINT8 = make(false,false,true , 8,0);
  public  static final TypeInt BOOL  = make(false,false,false, 1,0);
  public  static final TypeNil FALSE = TypeNil.XNIL;
  public  static final TypeInt TRUE  = con(1);
  public  static final TypeInt C3    = con(3);
  public  static final TypeInt C123  = con(123456789L);
  static final TypeInt[] TYPES = new TypeInt[]{INT64,NINT64,INT32,INT16,INT8,NINT8,BOOL,TRUE,C3,C123};
  static void init1( HashMap<String,Type> types ) {
    types.put("bool" ,BOOL);
    types.put("int1" ,BOOL);
    types.put("int8" ,INT8);
    types.put("int16",INT16);
    types.put("int32",INT32);
    types.put("int64",INT64);
    types.put("int"  ,INT64);
  }
  // Return a long from a TypeInt constant; assert otherwise.
  @Override public long   getl() { assert is_con(); return _con; }
  @Override public double getd() { assert is_con() && (long)((double)_con)==_con; return _con; }

  @Override protected TypeInt xdual() {
    boolean xor = _nil == _sub;
    return _z==0 ? this : POOLS[TINT].<TypeInt>malloc().init(!_any,_nil^xor,_sub^xor,_z,0);
  }
  @Override protected TypeInt xmeet( Type t ) {
    TypeInt ti = (TypeInt)t;
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

  private static int log( long con ) {
    if(     0 <= con && con <=     1 ) return  1;
    if(  -128 <= con && con <=   127 ) return  8;
    if(-32768 <= con && con <= 32767 ) return 16;
    if( Integer.MIN_VALUE <= con && con <= Integer.MAX_VALUE ) return 32;
    return 64;
  }

  @Override public TypeInt widen() { return INT64; }
  @Override public boolean is_con()  { return _z==0; }
  public TypeInt minsize(TypeInt ti) { throw unimpl(); } // smaller size of Prim AND
  public TypeInt maxsize(TypeInt ti) { return (TypeInt)meet(ti);  }
}
