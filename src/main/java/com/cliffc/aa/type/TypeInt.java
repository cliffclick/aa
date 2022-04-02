package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.HashMap;

import static com.cliffc.aa.AA.unimpl;

public class TypeInt extends Type<TypeInt> {
  private byte _x;        // -2 bot, -1 not-null, 0 con, +1 not-null-top +2 top
  public  byte _z;        // bitsiZe, one of: 1,8,16,32,64
  private long _con;      // hi or lo according to _x
  private TypeInt init(int x, int z, long con ) { _x=(byte)x; _z=(byte)z; _con = con; _name=""; return this; }
  @Override TypeInt copy() { return _copy().init(_x,_z,_con); }
  // Hash does not depend on other types
  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_x,_z,(int)_con); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeInt t2) ) return false;
    return super.equals(o) && _x==t2._x && _z==t2._z && _con==t2._con;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    sb.p(_name);
    if( _con != 0 ) return sb.p(_x<0 ? "&" : (_x>0 ? "+" : "")).p(_con);
    if( _x==0 ) return sb.p("0");
    return sb.p(_x>0?"~":"").p(Math.abs(_x)==1?"n":"").p("int").p(_z);
  }

  static Type valueOfInt(String cid) {
    return switch(cid) {
    case  "int64" ->  INT64;
    case "nint64" -> NINT64;
    case "nint8"  -> NINT8 ;
    case  "int1"  -> BOOL;
    default       -> null;
    };
  }

  static { new Pool(TINT,new TypeInt()); }
  public static TypeInt make( int x, int z, long con ) {
    assert con==0 || log(con)==z;
    if( Math.abs(x)==1 && z==1 && con==0) { con=1; x=0; } // not-null-bool is just a 1
    TypeInt t1 = POOLS[TINT].malloc();
    return t1.init(x,z,con).hashcons_free();
  }

  public static TypeInt con(long con) { return make(0,log(con),con); }

  static public  final TypeInt  INT64 = make(-2,64,0);
  static public  final TypeInt  INT32 = make(-2,32,0);
  static         final TypeInt  INT16 = make(-2,16,0);
  static public  final TypeInt  INT8  = make(-2, 8,0);
  static public  final TypeInt  BOOL  = make(-2, 1,0);
  static public  final TypeInt TRUE   = make( 0, 1,1);
  static public  final TypeInt FALSE  = make( 0, 1,0);
  static public  final TypeInt NINT8  = make(-1, 8,0);
  static public  final TypeInt NINT64 = make(-1,64,0);
  static public  final TypeInt ZERO   = FALSE;
  static public  final TypeInt C3     = make( 0, 8,3);
  static public  final TypeInt C123   = make( 0,32,123456789L);
  static final TypeInt[] TYPES = new TypeInt[]{INT64,NINT64,INT32,INT16,INT8,NINT8,BOOL,TRUE,ZERO,C3,C123};
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

  @Override protected TypeInt xdual() { return _x==0 ? this : POOLS[TINT].<TypeInt>malloc().init(-_x,_z,_con); }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    switch( t._type ) {
    case TINT:   break;
    case TFLT:   return xmeetf((TypeFlt)t);
    case TFUNPTR:
    case TMEMPTR:
    case TRPC:   return cross_nil(t);
    case TARY:
    case TFLD:
    case TSTRUCT:
    case TTUPLE:
    case TMEM:   return ALL;
    default: throw typerr(t);
    }
    TypeInt tt = (TypeInt)t;
    assert !equals(tt);         // Already covered by interning
    int maxz = Math.max(_z,tt._z);
    int minz = Math.min(_z,tt._z);
    if( _x== 0 && tt._x== 0 && _con==tt._con ) return make(0,maxz,_con);
    if( _x<= 0 && tt._x<= 0 ) return make(Math.min(nn(),tt.nn()),maxz,0); // Both bottom, widen size
    if( _x > 0 && tt._x > 0 ) return make(Math.min(  _x,tt._x  ),minz,0); // Both top, narrow size
    if( _x==-2 && tt._x== 2 ) return this; // Top loses to other guy
    if( _x== 2 && tt._x==-2 ) return tt  ; // Top loses to other guy

    // ttop==+1,+2 and that is 0,-1,-2
    TypeInt that = _x>0 ? tt : this;
    TypeInt ttop = _x>0 ? this : tt;
    if( that._x<0 ) return that; // Return low value
    if( log(that._con) <= ttop._z && (that._con!=0 || ttop._x==2) )
      return that;                    // Keep a fitting constant
    return make(that.nn(),that._z,0); // No longer a constant
  }

  private int nn() { assert _x <=0; return _con!=0 || _x== -1 ? -1 : -2; }
  private static int log( long con ) {
    if(     0 <= con && con <=     1 ) return  1;
    if(  -128 <= con && con <=   127 ) return  8;
    if(-32768 <= con && con <= 32767 ) return 16;
    if(Integer.MIN_VALUE <= con && con <= Integer.MAX_VALUE ) return 32;
    return 64;
  }

  Type xmeetf( TypeFlt tf ) {
    return switch( _x ) {
    case -2, -1 -> // Low int
      switch( tf._x ) {
      case -2,-1,0 -> _low(tf,Math.min(_x,tf._x)); // narrow ints fit in a fatter float; if both are fat go to Scalar
      case  1,2 -> this;  // high NZ float can pick '1', so any low int will do
      default -> throw unimpl();
      };
    case  0 ->                  // Constant integer
      switch( tf._x ) {
      case -2 -> _z<tf._z ? tf : (_z==32 ? TypeFlt.FLT64  : SCALAR); // narrow ints fit in a fatter float
      case -1 -> this==ZERO ? TypeFlt.make(-2,tf._z,0)
        : _z < tf._z ? tf : TypeFlt.NFLT64; // narrow ints fit in a fatter float
      case  0 -> this==ZERO         // no float constant is ever any int
        ? (tf._z==32 ? TypeFlt.FLT32 : TypeFlt.FLT64) // expand 0z to int1, mix with flt con
        : (tf._z==32 && _z<32 ? TypeFlt.NFLT32 : TypeFlt.NFLT64); // expand to int32, mix with flt con
      case  1 -> this==ZERO ? BOOL     // Zero vs NZ float
        : _z < tf._z ? this : TypeInt.make(-1,_z,0); // High float; con is OK if small enough
      case  2 -> _z < tf._z ? this : TypeInt.make(-1,_z,0); // High float; con is OK if small enough
      default -> throw unimpl();
      };
    case  1, 2 ->               // High int
      switch( tf._x ) {
      case -2, -1 -> tf;      // high int can pick '1', so any low float will do
      case  0 -> tf._z==32 ? TypeFlt.NFLT32 : TypeFlt.NFLT64; // high int can pick '1'
      case  1, 2 -> TypeInt.make( Math.min(_x,tf._x),Math.min(_z,tf._z>>1),0); // Pick smaller size in the ints
      default -> throw unimpl();
      };
    default -> throw unimpl();
    };
  }
  // narrow ints fit in a fatter float; if both are fat go to Scalar
  Type _low(TypeFlt tf, int nz) {
    return _z<tf._z && tf._z==32 ? TypeFlt.make(nz,32,0) : (_z<64 ? TypeFlt.make(nz,64,0) : (nz==-1 ? Type.NSCALR : Type.SCALAR));
  }

  @Override public Type _widen() { return INT64; }
  @Override public boolean above_center() { return _x>0; }
  @Override public boolean may_be_con() { return _x>=0; }
  @Override public boolean is_con()   { return _x==0; }
  @Override public boolean must_nil() { return _x==-2 || (_x==0 && _con==0); }
  @Override public boolean may_nil() { return _x==2; }
  @Override Type not_nil() {
    // Choice {+0+1} ==> {+1}, which is just {1}
    if( this==BOOL.dual() ) return TRUE;
    // {0} ==> {0,1}
    if( this==FALSE ) return BOOL;
    // Choice any-int ==> any-not-nil-int
    if( _x==2 ) return make(1,_z,_con);
    // Never had a nil choice
    return this;
  }
  @Override public Type remove_nil() {
    if( _x > 0 ) return this;
    if( _x==0 && _con!=0 ) return this; // Non-zero constant
    if( this==BOOL ) return TRUE; // Removing 0 from a range 0-1 leaves only 1
    throw unimpl();
  }
  @Override public Type meet_nil(Type nil) {
    if( nil==Type.XNIL )
      return _x==2 ? Type.XNIL : (_x==-2 || (_x==0&&_con==0)? Type.SCALAR : Type.NSCALR);
    return TypeInt.make(-2,_x<=0?_z:1,0);
  }
  public TypeInt minsize(TypeInt ti) { return make(-2,Math.min(_z,ti._z),0);  }
  public TypeInt maxsize(TypeInt ti) { return make(-2,Math.max(_z,ti._z),0);  }
}
