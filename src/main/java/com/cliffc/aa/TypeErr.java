package com.cliffc.aa;

/** Error data type.  If the program result is of this type, the program is not well formed. */
public class TypeErr extends Type {
  boolean _all;
  public String _msg;
  private Type _a,_b;           // Error !(a isa b)
  private TypeErr ( String msg, boolean all, Type a, Type b ) { super(TERROR); init(msg,all,a,b); }
  private void init(String msg, boolean all, Type a, Type b ) { _msg=msg; _all=all; _a=a; _b=b; }
  @Override public int hashCode( ) { return TERROR+_msg.hashCode()+(_all?1:0)+(_a==null?0:_a.hashCode()+_b.hashCode()); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeErr) ) return false;
    TypeErr t2 = (TypeErr)o;
    return _msg.equals(t2._msg) && _all==t2._all && _a==t2._a && _b==t2._b;
  }
  private static TypeErr FREE=null;
  private TypeErr free( TypeErr f ) { FREE=f; return this; }
  public static TypeErr make( String msg ) { return make(msg,null,null); }
  public static TypeErr make( String msg, Type a, Type b ) { return make(msg,true,a,b); }
  private static TypeErr make( String msg, boolean all, Type a, Type b ) {
    TypeErr t1 = FREE;
    if( t1 == null ) t1 = new TypeErr(msg,all,a,b);
    else { FREE = null; t1.init(msg,all,a,b); }
    TypeErr t2 = (TypeErr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static public final TypeErr ALL = make("all");
  static public final TypeErr ANY = make("all",false,null,null);

  static final TypeErr[] TYPES = new TypeErr[]{ANY,ALL};
  @Override protected TypeErr xdual() { return new TypeErr(_msg,!_all,_a==null?null:_a.dual(),_b==null?null:_b.dual()); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    if( t._type != TERROR ) return _all ? this : t; // Errors win over non-errors
    if( this==ALL || t==ANY ) return this;
    if( t==ALL || this==ANY ) return t   ;
    TypeErr te = (TypeErr)t;
    if( _msg.equals(te._msg) && _a==te._a && _b==te._b )
      return _all ? this : t;
    // Merge isa complaints
    if( _a != null ) {
      if( _all != te._all ) throw AA.unimpl(); // mixed-mode?
      if( !_all ) throw AA.unimpl(); // implement join-vs-meet
      Type a = _a.meet(te._a);
      Type b = _b.join(te._b);
      if( a==   _a && b==   _b ) return this;
      if( a==te._a && b==te._b ) return te;
      throw AA.unimpl();
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
