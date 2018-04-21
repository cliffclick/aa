package com.cliffc.aa;

public class TypeFlt extends Type {
  byte _x;                // -1 bot, 0 con, +1 top
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
  @Override public String toString() {
    if( _x==0 ) return Double.toString(_con);
    return (_x==1?"~":"")+"Flt"+Integer.toString(_z);
  }
  private static TypeFlt FREE=null;
  private TypeFlt free( TypeFlt f ) { FREE=f; return this; }
  public static TypeFlt make( int x, int z, double con ) {
    TypeFlt t1 = FREE;
    if( t1 == null ) t1 = new TypeFlt(x,z,con);
    else { FREE = null; t1.init(x,z,con); }
    TypeFlt t2 = (TypeFlt)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  public static TypeFlt con(double con) { return make(0,log(con),con); }
  
  static public final TypeFlt FLT64 = make(-1,64,0);
  static public final TypeFlt FLT32 = make(-1,32,0);
  static public final TypeFlt PI    = con(Math.PI);
  static final TypeFlt[] TYPES = new TypeFlt[]{FLT64,FLT32,PI};
  // Return a double from a TypeFlt constant; assert otherwise.
  @Override public double getd() { assert is_con(); return _con; }

  @Override protected TypeFlt xdual() { return _x==0 ? this : new TypeFlt(-_x,_z,_con); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    switch( t._type ) {
    case TFLT:   break;
    case TINT:   return ((TypeInt)t).xmeetf(this);
    case TFUN:   return Type.SCALAR;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TCONTROL:
    case TTUPLE: return TypeErr.ALL;
    case TUNION: return t.xmeet(this); // Let TypeUnion decide
    default: throw typerr(t);
    }
    TypeFlt tf = (TypeFlt)t;
    assert !equals(tf);         // Already covered by interning
    int maxz = Math.max(_z,tf._z);
    int minz = Math.min(_z,tf._z);
    if( _x== 0 && tf._x== 0 && _con==tf._con ) return make(0,maxz,_con);
    if( _x<= 0 && tf._x<= 0 ) return make(-1,maxz,0); // Both bottom, widen size
    if( _x==-1 && tf._x== 1 ) return this; // Top loses to other guy
    if( _x== 1 && tf._x==-1 ) return tf;   // Top loses to other guy
    if( _x== 1 && tf._x== 1 ) return make( 1,minz,0); // Both top, narrow size

    // constant meet top
    // _x==1 ==> tf is the constant, else _x==0 and is the constant
    TypeFlt tcon = _x==1 ? tf : this;
    TypeFlt ttop = _x==1 ? this : tf;
    if( log(tcon._con) <= ttop._z ) return tcon;
    return make(-1,maxz,0);
  }
  static int log( double con ) { return ((double)(float)con)==con ? 32 : 64; }
  
  @Override public boolean isBitShape(Type t) { return t._type == Type.TFLT && _z<=((TypeFlt)t)._z; }
  @Override public boolean above_center() { return _x>0; }
  @Override public boolean canBeConst() { return _x>=0; }
  @Override public boolean is_con()   { return _x==0; }
}
