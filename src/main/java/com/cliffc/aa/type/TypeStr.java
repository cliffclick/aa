package com.cliffc.aa.type;

import java.util.HashMap;

public class TypeStr extends Type {
  byte _x;                // -1 bot, 0 con, +1 top
  String _con;            // only if _x==0
  private TypeStr( int x, String con ) { super(TSTR); init(x,con); }
  private void init(int x, String con ) { _x=(byte)x; _con = con; }
  @Override public int hashCode( ) { return TSTR+_x+(_con==null ? 0 : _con.hashCode());  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStr) ) return false;
    TypeStr t2 = (TypeStr)o;
    return _x==t2._x && _con.equals(t2._con);
  }
  @Override public String toString() {
    if( _x==0 ) return "\""+_con+"\"";
    return (_x==1?"~":"")+"str";
  }
  private static TypeStr FREE=null;
  private TypeStr free( TypeStr f ) { FREE=f; return this; }
  public static TypeStr make( int x, String con ) {
    TypeStr t1 = FREE;
    if( t1 == null ) t1 = new TypeStr(x,con);
    else { FREE = null; t1.init(x,con); }
    TypeStr t2 = (TypeStr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  public static TypeStr con(String con) { return make(0,con); }

  static public final TypeStr STR = make(-1,null);
  static final TypeStr[] TYPES = new TypeStr[]{STR};
  static void init1( HashMap<String,Type> types ) {
    types.put("str",STR);
  }
  // Return a String from a TypeStr constant; assert otherwise.
  @Override public String getstr() { assert is_con(); return _con; }

  @Override protected TypeStr xdual() { return _x==0 ? this : new TypeStr(-_x,_con); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    switch( t._type ) {
    case TSTR:   break;
    case TFLT:
    case TINT:   return TypeUnion.make(false,this,t);
    case TSTRUCT:
    case TTUPLE: return Type.OOP;
    case TRPC:
    case TFUN:   return Type.SCALAR;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TCTRL:
    case TXCTRL: return TypeErr.ALL;
    case TNAME:
    case TUNION: return t.xmeet(this); // Let TypeUnion decide
    default: throw typerr(t);
    }
    TypeStr tt = (TypeStr)t;
    if( _x==tt._x && _con == tt._con ) return this;
    if( _x== 1 || tt._x==-1 ) return tt;
    if( _x==-1 || tt._x== 1 ) return this;
    return _con.equals(tt._con) ? this : STR;
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
    assert _x <= 0;
    return STR;
  }
  @Override public boolean above_center() { return _x>0; }
  @Override public boolean canBeConst() { return _x>=0; }
  @Override public boolean is_con()   { return _x==0; }
}
