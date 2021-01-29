package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;
import java.util.function.Predicate;

public class TypeInt extends Type<TypeInt> {
  private byte _x;        // -2 bot, -1 not-null, 0 con, +1 not-null-top +2 top
  public  byte _z;        // bitsiZe, one of: 1,8,16,32,64
  private long _con;      // hi or lo according to _x
  private TypeInt ( int x, int z, long con ) { super(TINT); init(x,z,con); }
  private void init(int x, int z, long con ) { super.init(TINT); _x=(byte)x; _z=(byte)z; _con = con; }
  // Hash does not depend on other types
  @Override int compute_hash() { return super.compute_hash()+_x+_z+(int)_con; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeInt) ) return false;
    TypeInt t2 = (TypeInt)o;
    return super.equals(o) && _x==t2._x && _z==t2._z && _con==t2._con;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    sb.p(_name);
    if( _con != 0 ) return sb.p(_x<0 ? "&" : (_x>0 ? "+" : "")).p(_con);
    if( _x==0 ) return sb.p(_con);
    return sb.p(_x>0?"~":"").p(Math.abs(_x)==1?"n":"").p("int").p(_z);
  }
  private static TypeInt FREE=null;
  @Override protected TypeInt free( TypeInt ret ) { FREE=this; return ret; }
  public static TypeInt make( int x, int z, long con ) {
    if( Math.abs(x)==1 && z==1 && con==0) con=1; // not-null-bool is just a 1
    TypeInt t1 = FREE;
    if( t1 == null ) t1 = new TypeInt(x,z,con);
    else {  FREE = null;      t1.init(x,z,con); }
    TypeInt t2 = (TypeInt)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeInt con(long con) { return make(0,log(con),con); }

  static public  final TypeInt  INT64 = make(-2,64,0);
  static public  final TypeInt  INT32 = make(-2,32,0);
  static         final TypeInt  INT16 = make(-2,16,0);
  static public  final TypeInt  INT8  = make(-2, 8,0);
  static public  final TypeInt  BOOL  = make(-2, 1,0);
  static public  final TypeInt TRUE   = make( 0, 1,1);
  static public  final Type    FALSE  = make( 0, 1,0);
  static public  final TypeInt XINT1  = make( 2, 1,0);
  static public  final TypeInt NINT8  = make(-1, 8,0);
  static public  final TypeInt NINT64 = make(-1,64,0);
  static public  final TypeInt ZERO   = (TypeInt)new TypeInt(0,1,0).hashcons();
  static final TypeInt[] TYPES = new TypeInt[]{INT64,INT32,INT16,BOOL,TRUE,XINT1,NINT64};
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

  @Override protected TypeInt xdual() { return _x==0 ? this : new TypeInt(-_x,_z,_con); }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    switch( t._type ) {
    case TINT:   break;
    case TFLT:   return xmeetf((TypeFlt)t);
    case TFUNPTR:
    case TMEMPTR:
    case TRPC:   return cross_nil(t);
    case TFUNSIG:
    case TARY:
    case TLIVE:
    case TOBJ:
    case TSTR:
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
    int tx = _x;
    if( tx > 0 ) {                // Top Int, size 1 to 64
      if( tf._x < 0 ) return tf; // (~Int | Flt) = Flt // choice includes 1 which is in all flts
      if( tf._x > 0 ) // ~Int | ~Flt = ~Int of some type; defaults to Int tossing all the non-integral Flt choices
        return make(Math.min(_x,tf._x),Math.min(tf._z>>1,_z),0); // Choices limited to smaller-ints (to fit in float of same range)
      // Float constant: cast "for free" to Int constant if possible, else fall to same as Flt-bottom
      long con = (long)tf._con;
      // Fits in the int choices, just keep float, but could return the int constant just as well
      if( con == tf._con && log(con) <= _z )  return tf;
      return TypeFlt.make(con==0 ? -2 : -1, tf._z,0);
    }

    if( tx == 0 ) {             // Constant int
      int lg = log(_con);
      if( tf._x< 0) {           // Bottom float/double
        // Wider of (ints-wider-by-1) and floats
        if( (lg<<1) <= tf._z ) return TypeFlt.make((_con!=0 && tf._x==-1) ? -1 : -2, tf._z,0); // Fits in a float
        return REAL;
      }
      if( tf._x== 0 ) {         // Int constant vs Float constant
        if( _con==tf._con ) return this; // Matching int constant wins
        if( ((long)tf._con) == tf._con ) // Float is a integer
          return xmeet(TypeInt.con((long)tf._con)); // Return as-if meeting 2 integers
        return TypeFlt.make(_con==0 || tf._con==0 ? -2 : -1,Math.max(TypeFlt.log(_con),tf._z),0);
      }
      // tf._x > 0 // Can a high float fall to the int constant?
      double dcon = tf._z==32 ? (float)_con : (double)_con;
      if( (long)dcon == _con && (_con!=0 || tf._x == 2) )
        return this;
      tx = _con==0 ? -2 : -1; // Fall from constant
    } // Fall into the bottom-int case

    // Bottom Int or constant did not fit, size 1 to 64
    if( tf._x > 0 ) return make(tx,_z,0); // ( Int | ~Flt) = Int, since can choose 1.0
    // Float constant: cast "for free" to Int if possible, else fall to same as Flt-bottom
    long icon = (long)tf._con;
    if( tf._x== 0 && icon == tf._con )
      return make(-2,Math.max(_z,log(icon)),0);
    if( (_z<<1) <= tf._z ) return TypeFlt.make(Math.min(tx,tf._x),tf._z,0);
    if( (_z<<1) <= 64 ) return TypeFlt.FLT64; // Fits in the float
    return must_nil() || tf.must_nil() ? REAL : NREAL;
  }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  @Override public byte isBitShape(Type t) {
    // TODO: Allow loss-less conversions (e.g. small float integer constants convert to ints just fine)
    if( t._type == TXSCALAR ) return 0;
    if( t._type == TINT ) return (byte)(_z<=((TypeInt)t)._z ? 0 : 99);
    if( t._type == TFLT ) return 2; // Int->Flt ignores large int overflow issues
    if( t._type == Type.TMEMPTR ) return 99; // No flt->ptr conversion
    if( t._type == Type.TFUNPTR ) return 99; // No flt->ptr conversion
    if( t._type == TREAL ) return 1;
    if( t._type == TSCALAR ) return 9; // Might have to autobox
    if( t._type == TSTR ) return 99;
    if( t == NIL || t == XNIL ) return 99; // Cannot not-nil to nil
    throw com.cliffc.aa.AA.unimpl();
  }
  @Override public Type widen() {
    assert _x <= 0;
    return INT64;
  }
  @Override public boolean above_center() { return _x>0; }
  @Override public boolean may_be_con() { return _x>=0; }
  @Override public boolean is_con()   { return _x==0; }
  @Override public boolean must_nil() { return _x==-2 || (_x==0 && _con==0); }
  @Override public boolean may_nil() { return _x>0 || (_x==0 && _con==0); }
  @Override Type not_nil() {
    // Choice {+0+1} ==> {+1}
    if( this==BOOL.dual() ) return make(1,1,1);
    // {0} ==> {0,1}
    if( this==FALSE ) return BOOL;
    // Choice any-int ==> any-not-nil-int
    if( _x==2 ) return make(1,_z,_con);
    // Never had a nil choice
    return this;
  }
  @Override public Type meet_nil(Type nil) {
    if( _x==2 ) return nil;
    if( _x==0 && _con==0 ) return nil==Type.XNIL ? this : Type.NIL;
    return TypeInt.make(-2,_z,0);
  }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
  public TypeInt minsize(TypeInt ti) { return make(-2,Math.min(_z,ti._z),0);  }
  public TypeInt maxsize(TypeInt ti) { return make(-2,Math.max(_z,ti._z),0);  }
}
