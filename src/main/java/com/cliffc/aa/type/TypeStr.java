package com.cliffc.aa.type;

import java.util.HashMap;

public class TypeStr extends Type {
  byte _x;                // -1 bot, 1 con, 0 top
  String _con;            // if con then any string, else if null is allowed then null else "" 
  private TypeStr( int x, String con ) { super(TSTR); init(x,con); }
  private void init(int x, String con ) {
    assert x!=1 || con!=null; // Disallow constant null string, use unified null instead
    _x=(byte)x;
    _con = con;
  }
  @Override public int hashCode( ) { return TSTR+_x+(_con==null ? 0 : _con.hashCode());  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStr) ) return false;
    TypeStr t2 = (TypeStr)o;
    return _x==t2._x && (_con==t2._con|| (_con!=null &&_con.equals(t2._con)));
  }
  @Override public String toString() {
    if( _x==1 ) return _con==null ? "null" : "\""+_con+"\"";
    return (_x==0?"~":"")+"str"+(_con!=null?"":(_x==0?"+":"")+"?");
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
  public static TypeStr con(String con) { return make(1,con); }

  static public final TypeStr STR0 = make(-1,null); // yes null
  static public final TypeStr STR  = make(-1,""  ); // no  null
  static final TypeStr[] TYPES = new TypeStr[]{STR,STR0};
  static void init1( HashMap<String,Type> types ) {
    types.put("str",STR);
  }
  // Return a String from a TypeStr constant; assert otherwise.
  @Override public String getstr() { assert is_con(); return _con; }

  @Override protected TypeStr xdual() { return _x==1 ? this : new TypeStr(-1-_x,_con); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    switch( t._type ) {
    case TSTR:   break;
    case TFLT:
    case TINT:
    case TSTRUCT:
    case TTUPLE:
      if(   may_be_null() ) return t.meet(TypeInt.NULL);
      if( t.may_be_null() ) return   make_null();
      return t._type==TFLT||t._type==TINT ? SCALAR : OOP0;
    case TRPC:
    case TFUN:   return SCALAR;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TNAME:  
    case TUNION: return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    TypeStr ts = (TypeStr)t;
    if( _x==ts._x && _con == ts._con ) return this;
    int x = _x | ts._x;
    String s = (_con==null || ts._con==null) ? null : (_con.equals(ts._con) ? _con : "");
    if( x == 0 ) {              // null test reversed for top result
      if( _con!=null || ts._con!=null ) s = "";
    }
    if( x == 1 ) {              // Possible constant needs more testing
      if( false ) ;
      else if(    _x==0 ) s = ts._con; // If either is top, take the other constant
      else if( ts._x==0 ) s =    _con;
      else if( _con!=null && ts._con!=null && !_con.equals(ts._con) )
        { x = -1; s=""; } // If both not-null but constants unequal, fall to bottom
    }
    return TypeStr.make(x,s);
  }

  // Add a null in
  public Type make_null() { return _x==0 && _con==null ? TypeInt.NULL : STR0; }
  
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
    return _con==null ? STR : STR0;
  }
  @Override public boolean above_center() { return _x==0; }
  @Override public boolean canBeConst() { return _x>=0; }
  @Override public boolean is_con()   { return _x==1; }
  @Override public boolean may_be_null() { return _x==0 && _con==null; }
}
