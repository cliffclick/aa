package com.cliffc.aa;

public class TypeErr extends Type {
  String _msg;
  private TypeErr( String msg ) { super(TERROR); init(msg); }
  private void init(String msg ) { _msg=msg; }
  @Override public int hashCode( ) { return TERROR+_msg.hashCode();  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeErr) ) return false;
    TypeErr t2 = (TypeErr)o;
    return _msg.equals(t2._msg);
  }
  @Override public String toString() { return _msg; }
  private static TypeErr FREE=null;
  private TypeErr free( TypeErr f ) { FREE=f; return this; }
  public static TypeErr make( String msg ) {
    TypeErr t1 = FREE;
    if( t1 == null ) t1 = new TypeErr(msg);
    else { FREE = null; t1.init(msg); }
    TypeErr t2 = (TypeErr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static public final TypeErr FAIL = make("fail");
  static final TypeErr[] TYPES = new TypeErr[]{FAIL};
  @Override protected TypeErr xdual() { return this; }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    if( t._type != TERROR ) return this;
    if( t   ==FAIL ) return this;
    if( this==FAIL ) return t   ;
    // Merge error messages?
    throw AA.unimpl();
  }

  @Override public boolean isBitShape(Type t) { return true; }
  @Override public boolean above_center() { return false; }
  @Override public boolean canBeConst() { return false; }
  @Override public boolean is_con()   { return false; }
}
