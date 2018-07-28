package com.cliffc.aa.type;

import java.util.HashMap;

public class TypeOop extends Type {
  byte _o; // 0=OOP&nil, 1=OOP, 2=nil, 3=OOP+nil
  private TypeOop ( byte type, byte o ) { super(o); init(type,o); }
  private void init(byte type, byte o ) { _type=type;  _o=o; }
  @Override public int hashCode( ) { return (_type<<8)+_o; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeOop) ) return false;
    TypeOop t2 = (TypeOop)o;
    return _type==t2._type && _o==t2._o;
  }
  private static final String[] TSTRS=new String[]{"oop?","oop","0","oop!"};
  @Override public String toString() { return TSTRS[_o]; }
  private static TypeOop FREE=nil;
  private TypeOop free( TypeOop f ) { FREE=f; return this; }
  public static TypeOop make( byte type, byte o ) {
    TypeOop t1 = FREE;
    if( t1 == nil ) t1 = new TypeOop(type,o);
    else { FREE = nil; t1.init(type,o); }
    TypeOop t2 = (TypeOop)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  private static TypeOop make( byte o ) { return make(TOOP,o); }
  static public final TypeOop OOP0 = make(0); // OOP&nil
  static public final TypeOop OOP  = make(1); // OOP
  static public final TypeOop NIL  = make(2); // nil
  static public final TypeOop OOP_ = make(3); // OOP+nil
  static final TypeOop[] TYPES = new TypeOop[]{OOP0,OOP,NIL,OOP_};

  @Override protected TypeOop xdual() {
    switch( _o ) {
    case 0: return new TypeOop(TOOP,3);
    case 1: case 2: return this;
    case 3: return new TypeOop(TOOP,0);
    default: throw typerr(this);
    }
  }
      
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    switch( t._type ) {
    case TOOP:
    case TSTRUCT:
    case TTUPLE:
    case TSTR:
      break;
    case TFLT:
    case TINT:
      //if(   may_be_nil() ) return t.meet(TypeInt.NIL);
      //if( t.may_be_nil() ) return   make_nil();
      //return t._type==TFLT||t._type==TINT ? SCALAR : OOP0;
      throw com.cliffc.aa.AA.unimpl();
    case TRPC:
    case TFUN:   return SCALAR;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TNAME:  
    case TUNION: return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    throw com.cliffc.aa.AA.unimpl();
  }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Str); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Str.
  //  0 requires no/free conversion (Str->Str)
  // +1 requires a bit-changing conversion; no auto-unboxing
  // 99 Bottom; No free converts; e.g. Flt->Str requires explicit rounding
  @Override public byte isBitShape(Type t) {
    if( t._type==Type.TSTR ) return 0;
    if( t instanceof TypeUnion && this.isa(t) )
      return 0;
    return 99;
  }
  @Override public Type widen() {
    assert _x != 0;
    return _con==nil ? STR : STR0;
  }
  @Override public boolean above_center() { return _x==0; }
  @Override public boolean canBeConst() { return _x>=0; }
  @Override public boolean is_con()   { return _x==1; }
  @Override public boolean may_be_nil() { return _x==0 && _con==nil; }
}
