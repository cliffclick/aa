package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;

public class TypeFlt extends Type<TypeFlt> {
  double _lo, _hi;              // float or double con according
  private TypeFlt ( double lo, double hi ) { super(TFLT); init(lo,hi); }
  private void init(double lo, double hi ) { super.init(TFLT); _lo=lo; _hi=hi; }
  // Hash does not depend on other types
  @Override int compute_hash() { return super.compute_hash()+(int)Double.doubleToRawLongBits(_lo)+(int)Double.doubleToRawLongBits(_hi); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFlt) ) return false;
    TypeFlt t2 = (TypeFlt)o;
    return super.equals(o) && _lo==t2._lo && _hi==t2._hi;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    sb.p(_name);
    if( _lo==_hi ) return sb.p(_lo);
    if( this==FLT64 )        return sb.p( "flt64");
    if( this==FLT64.dual() ) return sb.p("~flt64");
    if( this==FLT32 )        return sb.p( "flt32");
    if( this==FLT32.dual() ) return sb.p("~flt32");
    if( _lo < _hi ) return sb.p('[').p(_lo).p('-').p(_hi).p(']');
    return sb.p("[-inf-").p(_hi).p(',').p(_lo).p("-+inf]");
  }
  private static TypeFlt FREE=null;
  @Override protected TypeFlt free( TypeFlt ret ) { FREE=this; return ret; }
  public static Type make( double lo, double hi ) {
    TypeFlt t1 = FREE;
    if( t1 == null ) t1 = new TypeFlt(lo,hi);
    else {  FREE = null;      t1.init(lo,hi); }
    TypeFlt t2 = (TypeFlt)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static Type con(double con) { return make(con,con); }

  public static final TypeFlt FLT64 = (TypeFlt)make(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY);
  public static final TypeFlt FLT32 = (TypeFlt)make(Float .NEGATIVE_INFINITY,Float .POSITIVE_INFINITY);
  public static final TypeFlt PI    = (TypeFlt)con(Math.PI);
  public static final TypeFlt HALF  = (TypeFlt)con(0.5);
  public static final TypeFlt[] TYPES = new TypeFlt[]{FLT64,FLT32,PI,HALF};
  static void init1( HashMap<String,Type> types ) {
    types.put("flt32",FLT32);
    types.put("flt64",FLT64);
    types.put("flt"  ,FLT64);
  }
  // Return a double from a TypeFlt constant; assert otherwise.
  @Override public boolean is_con() { return _lo==_hi; }
  @Override public double getd() { assert is_con(); return _lo; }
  @Override public long   getl() { assert is_con() && ((long)_lo)==_lo; return (long)_lo; }

  @Override protected TypeFlt xdual() { return is_con() ? this : new TypeFlt(_hi,_lo); }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    switch( t._type ) {
    case TFLT:   break;
    case TINT:   return ((TypeInt)t).xmeetf(this);
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
    TypeFlt tf = (TypeFlt)t;
    // Handle the 64-bit top/bot endpoints
    return make(Math.min(_lo,tf._lo),Math.max(_hi,tf._hi));
  }

  @Override public boolean above_center() { return _hi < _lo; }
  @Override public boolean may_be_con() { return _hi <= _lo; }
  @Override public boolean must_nil() { return _lo <= 0 && 0 <= _hi; }
  @Override public boolean  may_nil() { return _hi <= 0 && 0 <= _lo; }
  @Override Type not_nil() { return this; }
  @Override public Type meet_nil(Type nil) {
    //if( _x==2 ) return nil;
    //if( _x==0 && _con==0 ) return nil==Type.XNIL ? this : Type.NIL;
    //return TypeFlt.make(-2,_z,0);
    throw unimpl();
  }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  @Override public byte isBitShape(Type t) {
    // TODO: Allow loss-less conversions (e.g. small float integer constants convert to ints just fine)
    if( t._type == Type.TFLT ) return 0;
    if( t._type == Type.TINT ) return 99; // Flt->Int always requires user intervention
    if( t._type == Type.TMEMPTR ) return 99; // No flt->ptr conversion
    if( t._type == Type.TFUNPTR ) return 99; // No flt->ptr conversion
    if( t._type == Type.TREAL ) return 1;
    if( t._type == TSCALAR ) return 9; // Might have to autobox
    throw com.cliffc.aa.AA.unimpl();
  }
  @Override public Type widen() { return FLT64; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
  boolean includes_int() {
    long rlo = Math.round(_lo);
    long rhi = Math.round(_hi);
    return rlo!=rhi || _lo==rlo || _hi==rhi;
  }
}
