package com.cliffc.aa;

/** Error data type.  If the program result is of this type, the program is not well formed. */
public class TypeErr extends Type {
  boolean _all;
  public String _msg;
  private Type _t;              // Optional type involved in the error
  private TypeErr ( String msg, boolean all, Type t ) { super(TERROR); init(msg,all,t); }
  private void init(String msg, boolean all, Type t ) { _msg=msg; _all=all; _t=t; }
  @Override public int hashCode( ) { return TERROR+_msg.hashCode()+(_all?1:0)+(_t==null?0:_t.hashCode()); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeErr) ) return false;
    TypeErr t2 = (TypeErr)o;
    return _msg.equals(t2._msg) && _all==t2._all && _t==t2._t;
  }
  private static TypeErr FREE=null;
  private TypeErr free( TypeErr f ) { FREE=f; return this; }
  public static TypeErr make( String msg ) { return make(msg,null); }
  public static TypeErr make( String msg, Type t ) { return make(msg,true,t); }
  private static TypeErr make( String msg, boolean all, Type t ) {
    TypeErr t1 = FREE;
    if( t1 == null ) t1 = new TypeErr(msg,all,t);
    else { FREE = null; t1.init(msg,all,t); }
    TypeErr t2 = (TypeErr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static public final TypeErr ALL = make("all");
  static public final TypeErr ANY = make("all",false,null);

  static final TypeErr[] TYPES = new TypeErr[]{ANY,ALL};
  @Override protected TypeErr xdual() { return new TypeErr(_msg,!_all,_t==null?null:_t.dual()); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    if( !_all ) return t;       // Anything-meet-ANY is that thing
    if( t._type != TERROR ) return this; // Anything-meet-ALL is ALL
    TypeErr te = (TypeErr)t;
    if( !te._all ) return this; // Anything-meet-ANY is that thing; dropping the 'any' error message
    // Keep the more generic error message (since this is meet not join)
    if( t   ==ALL || this==ALL) return ALL;
    // If a specific error type is involved, and one isa the other return the other.
    if( _t != null && te._t != null ) {
      if( _t.isa(te._t) ) return te;
      if( te._t.isa(_t) ) return this;
    }
    // Merge error messages?
    throw AA.unimpl();
  }

  @Override public byte isBitShape(Type t) { return -1; }
  @Override public String toString() { return this==ANY ? "any" : ((_all ? "" : "~")+ _msg); }
  @Override public boolean above_center() { return !_all; }
  @Override public boolean canBeConst() { return !_all; }
  @Override public boolean is_con()   { return false; }
}
