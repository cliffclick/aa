package com.cliffc.aa.type;

import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Predicate;

public class TypeFlt extends Type<TypeFlt> {
  byte _x;                // -2 bot, -1 not-null, 0 con, +1 not-null-top +2 top
  byte _z;                // bitsiZe, one of: 32,64
  double _con;
  private TypeFlt( int x, int z, double con ) { super(TFLT); init(x,z,con); }
  private void init(int x, int z, double con ) { _x=(byte)x; _z=(byte)z; _con = con; }
  @Override public int hashCode( ) { return TFLT+_x+_z+(int)_con;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFlt) ) return false;
    TypeFlt t2 = (TypeFlt)o;
    return _x==t2._x && _z==t2._z && _con==t2._con;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    if( _x==0 ) return Double.toString(_con);
    return (_x>0?"~":"")+(Math.abs(_x)==1?"n":"")+"flt"+Integer.toString(_z);
  }
  private static TypeFlt FREE=null;
  @Override protected TypeFlt free( TypeFlt ret ) { FREE=this; return ret; }
  public static TypeFlt make( int x, int z, double con ) {
    TypeFlt t1 = FREE;
    if( t1 == null ) t1 = new TypeFlt(x,z,con);
    else { FREE = null; t1.init(x,z,con); }
    TypeFlt t2 = (TypeFlt)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeFlt con(double con) { return make(0,log(con),con); }
  
  public static final TypeFlt FLT64 = make(-2,64,0);
  public static final TypeFlt FLT32 = make(-2,32,0);
  public static final TypeFlt PI    = con(Math.PI);
  public static final TypeFlt NFLT64= make(-1,64,0);
  public static final TypeFlt[] TYPES = new TypeFlt[]{FLT64,FLT32,PI,NFLT64};
  static void init1( HashMap<String,Type> types ) {
    types.put("flt32",FLT32);
    types.put("flt64",FLT64);
    types.put("flt"  ,FLT64);
  }
  // Return a double from a TypeFlt constant; assert otherwise.
  @Override public double getd() { assert is_con(); return _con; }
  @Override public long   getl() { assert is_con() && ((long)_con)==_con; return (long)_con; }

  @Override protected TypeFlt xdual() { return _x==0 ? this : new TypeFlt(-_x,_z,_con); }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    switch( t._type ) {
    case TFLT:   break;
    case TINT:   return ((TypeInt)t).xmeetf(this);
    case TOOP:
    case TSTR:
    case TSTRUCT:
    case TTUPLE:
    case TFUNPTR:
    case TFUN:
    case TRPC:   return must_nil() ? SCALAR : NSCALR;
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    TypeFlt tf = (TypeFlt)t;
    assert !equals(tf);         // Already covered by interning
    int maxz = Math.max(_z,tf._z);
    int minz = Math.min(_z,tf._z);
    if( _x== 0 && tf._x== 0 && _con==tf._con ) return make(0,maxz,_con);
    if( _x<= 0 && tf._x<= 0 ) return make(Math.min(nn(),tf.nn()),maxz,0); // Both bottom, widen size
    if( _x > 0 && tf._x > 0 ) return make(Math.min(_x,tf._x),minz,0); // Both top, narrow size
    if( _x==-2 && tf._x== 2 ) return this; // Top loses to other guy
    if( _x== 2 && tf._x==-2 ) return tf;   // Top loses to other guy

    // ttop==+1,+2 and that is 0,-1,-2
    TypeFlt that = _x>0 ? tf : this;
    TypeFlt ttop = _x>0 ? this : tf;
    if( that._x<0 ) return that; // Return low value
    if( log(that._con) <= ttop._z && (that._con!=0 || ttop._x==2) )
      return that;            // Keep a fitting constant
    return make(that.nn(),that._z,0); // No longer a constant
  }
  private int nn() { assert _x <=0; return _con!=0 || _x== -1 ? -1 : -2; }
  private static int log( double con ) { return ((double)(float)con)==con ? 32 : 64; }
  
  @Override public boolean above_center() { return _x>0; }
  @Override public boolean may_be_con() { return _x>=0; }
  @Override public boolean is_con()   { return _x==0; }
  @Override boolean must_nil() { assert _x!=0||_con!=0; return _x==-2; }
  @Override Type not_nil(Type ignore) { return _x==2 ? make(1,_z,_con) : this; }
  @Override Type meet_nil() { return meet(TypeInt.FALSE); }
  
  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  @Override public byte isBitShape(Type t) {
    // TODO: Allow loss-less conversions (e.g. small float integer constants convert to ints just fine)
    if( t._type == Type.TFLT ) return (byte)(_z<=((TypeFlt)t)._z ? 0 : 99);
    if( t._type == Type.TINT ) return 99; // Flt->Int always requires user intervention
    if( t._type == Type.TREAL ) return 1;
    if( t._type == Type.TSCALAR ) return 1;
    throw com.cliffc.aa.AA.unimpl();
  }
  @Override public Type widen() {
    assert _x <= 0;
    return FLT64;
  }
  @Override Type make_recur(TypeName tn, int d, BitSet bs ) { return this; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
