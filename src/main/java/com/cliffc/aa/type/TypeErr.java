package com.cliffc.aa.type;

/** Error data type.  If the program result is of this type, the program is not well formed. */
public class TypeErr extends Type {
  boolean _all, _multi;         // Above or below centerline/dual; multiple errors (of which _msg is one)
  public String _msg;
  private Type _a,_b;           // Error !(a isa b)
  private TypeErr ( String msg, boolean all, Type a, Type b, boolean multi ) { super(TERROR); init(msg,all,a,b,multi); }
  private void init(String msg, boolean all, Type a, Type b, boolean multi ) { _msg=msg; _all=all; _a=a; _b=b; _multi=multi;}
  @Override public int hashCode( ) { return TERROR+_msg.hashCode()+(_all?1:0)+(_a==null?0:_a.hashCode()+_b.hashCode())+(_multi?2:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeErr) ) return false;
    TypeErr t2 = (TypeErr)o;
    return _msg.equals(t2._msg) && _all==t2._all && _a==t2._a && _b==t2._b && _multi==t2._multi;
  }
  @Override public String toString() { return this==ANY ? "any" : ((_all ? "" : "~")+ _msg + (_multi ? "+++" : "")); }
  private static TypeErr FREE=null;
  private TypeErr free( TypeErr f ) { FREE=f; return this; }
  public static TypeErr make( String msg ) { return make(msg,null,null,false); }
  public static TypeErr make( String msg, Type a, Type b, boolean multi ) { return make(msg,true,a,b,multi); }
  private static TypeErr make( String msg, boolean all, Type a, Type b, boolean multi ) {
    TypeErr t1 = FREE;
    if( t1 == null ) t1 = new TypeErr(msg,all,a,b,multi);
    else { FREE = null; t1.init(msg,all,a,b,multi); }
    TypeErr t2 = (TypeErr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static public final TypeErr ALL = make("all");
  static public final TypeErr ANY = make("all",false,null,null,false);

  static final TypeErr[] TYPES = new TypeErr[]{ANY,ALL};
  @Override protected TypeErr xdual() { return new TypeErr(_msg,!_all,_a==null?null:_a.dual(),_b==null?null:_b.dual(),_multi); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    if( t._type != TERROR ) return _all ? this : t; // Errors win over non-errors
    if( this==ALL || t==ANY ) return this;
    if( t==ALL || this==ANY ) return t   ;
    TypeErr te = (TypeErr)t;
    if( _msg.equals(te._msg) && _a==te._a && _b==te._b && _multi==te._multi)
      return _all ? this : t;
    if( _all != te._all ) throw com.cliffc.aa.AA.unimpl(); // mixed-mode?
    // Merge isa complaints
    Type a=null, b=null;
    if( _a != null ) {
      a = _all ? _a.meet(te._a) : _a.join(te._a);
      b = _all ? _b.join(te._b) : _b.meet(te._b);
    }
    // Merge errors
    boolean multi = _multi | te._multi; // If either is a multi, so is the result
    String msg = _msg;
    if( !_msg.equals(te._msg) ) {
      multi = true;             // If strings are unequal, result is a multi
      if( msg.compareTo(te._msg) > 0 ) msg = te._msg; // And take alpha-sort string only
    }
    return make(msg, _all|te._all, a, b, multi);
  }
  @Override public boolean above_center() { return !_all; }
  @Override public boolean may_be_con() { return !_all; }
  @Override public boolean is_con()   { return !_all; }
  @Override public byte isBitShape(Type t) { return _all && this!=ALL ? (byte)99 : -1; }
  @Override public String errMsg() { return above_center() || this==ALL ? null : _msg; }
}
