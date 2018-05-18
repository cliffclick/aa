package com.cliffc.aa;

/** Error data type.  If the program result is of this type, the program is not well formed. */
public class TypeErr extends Type {
  boolean _all;
  String _msg;
  private TypeErr( String msg, boolean all ) { super(TERROR); init(msg,all); }
  private void init(String msg, boolean all ) { _msg=msg; _all=all; }
  @Override public int hashCode( ) { return TERROR+_msg.hashCode()+(_all?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeErr) ) return false;
    TypeErr t2 = (TypeErr)o;
    return _msg.equals(t2._msg) && _all==t2._all;
  }
  private static TypeErr FREE=null;
  private TypeErr free( TypeErr f ) { FREE=f; return this; }
  public static TypeErr make( String msg ) { return make(msg,true); }
  public static TypeErr make( String msg, boolean all ) {
    TypeErr t1 = FREE;
    if( t1 == null ) t1 = new TypeErr(msg,all);
    else { FREE = null; t1.init(msg,all); }
    TypeErr t2 = (TypeErr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static public final TypeErr ALL = make("all");
  static public final TypeErr ANY = make("all",false);

  static final TypeErr[] TYPES = new TypeErr[]{ANY,ALL};
  @Override protected TypeErr xdual() { return new TypeErr(_msg,!_all); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    if( !_all ) return t;       // Anything-meet-ANY is that thing
    if( t._type != TERROR ) return this; // Anything-meet-ALL is ALL
    TypeErr te = (TypeErr)t;
    if( !te._all ) return this; // Anything-meet-ANY is that thing; dropping the 'any' error message
    // Keep the more generic error message (since this is meet not join)
    if( t   ==ALL || this==ALL) return ALL;
    // Merge error messages?
    throw AA.unimpl();
  }

  @Override public byte isBitShape(Type t) { return -1; }
  @Override public String toString() { return (_all ? "" : "~")+ _msg; }
  @Override public boolean above_center() { return !_all; }
  @Override public boolean canBeConst() { return !_all; }
  @Override public boolean is_con()   { return false; }
}
