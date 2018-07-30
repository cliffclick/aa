package com.cliffc.aa.type;

public class TypeName extends Type {
  public  String _name;
  public  Type _t;
  private short _depth;
  private TypeName ( String name, Type t ) { super(TNAME); init(name,t); }
  private void init( String name, Type t ) { _name=name; _t=t; _depth = (short)(t instanceof TypeName ? ((TypeName)t)._depth+1 : 0); }
  @Override public int hashCode( ) { return TNAME+(_name==null?0:_name.hashCode())+_t.hashCode()+_depth;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeName) ) return false;
    TypeName t2 = (TypeName)o;
    return _t==t2._t && _depth==t2._depth && (_name==t2._name || (_name!=null && _name.equals(t2._name)));
  }
  @Override public String toString() {
    String n = _name==null ? "^" : (_name.isEmpty() ? "_" : _name);
    return n+":"+_t;
  }
  private static TypeName FREE=null;
  private TypeName free( TypeName f ) { FREE=f; return this; }
  private static TypeName make( String name, Type t) {
    assert !(t instanceof TypeUnion); // No named unions
    assert t!=TypeInt.NULL;           // No named null
    TypeName t1 = FREE;
    if( t1 == null ) t1 = new TypeName(name,t);
    else { FREE = null; t1.init(name,t); }
    TypeName t2 = (TypeName)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  public static Type make0( String name, Type t ) {
    if( t==TypeInt.NULL ) return t; // No named null
    String dname = defarg(t);
    if( t.is_simple() || name==dname || (name!=null && name.equals(dname)) )
      return t;
    return make(name,t);
  }

  static public  final TypeName TEST_ENUM = make("__test_enum",TypeInt.INT8);
  static private final TypeName TEST_FLT  = make("__test_flt" ,TypeFlt.FLT32);
  static private final TypeName TEST_E2   = make("__test_e2"  ,TEST_ENUM);
  
  static final TypeName[] TYPES = new TypeName[]{TEST_ENUM,TEST_FLT,TEST_E2};

  @Override protected TypeName xdual() {
    String dname = sdual(_name);
    return dname==_name && _t==_t.dual() ? this : new TypeName(dname,_t.dual());
  }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    switch( t._type ) {
    case TNAME:
      TypeName tn = (TypeName)t;
      if( tn._depth > _depth ) return tn.xmeet(this); // Deeper on 'this'
      if( tn._depth== _depth )
        return make0( smeet(_name,tn._name), _t.meet(tn._t));
      break;
    case TUNION: return t.xmeet(this); // Let TypeUnion decide
    case TERROR: return ((TypeErr)t)._all ? t : this;
    default: break;
    }
    // LHS is named, RHS is unnamed.
    if( _t.may_be_nil() && !t.may_be_nil() )
      return TypeInt.NULL.meet(t); // Degrade LHS to a null and drop the _name
    Type mt = _t.meet(t);       // Peel and meet; keep name if RHS is above-or-null
    return t.may_be_nil() ? make0(_name,mt) : mt;
  }
  static String sdual( String s ) {
    if( s==null ) return "";
    if( s.isEmpty() ) return null;
    return s;
  }
  // Default arg (top or bottom) if no arg is available
  static String defarg( Type t ) { return ((t.above_center() && t!=Type.XCTRL)) ? null : ""; }
  // String meet; empty string is bottom; null is top
  static String smeet( String s0, String s1 ) {
    if( s0==s1 ) return s0;
    if( s0==null ) return s1;
    if( s1==null ) return s0;
    if( s0.isEmpty() ) return s0;
    if( s1.isEmpty() ) return s1;
    if( s0.equals(s1) ) return s0;
    return "";
  }

  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean canBeConst() { return _t.canBeConst(); }
  @Override public boolean is_con()   { return _t.is_con(); }
  @Override public double getd  () { return _t.getd  (); }
  @Override public long   getl  () { return _t.getl  (); }
  @Override public String getstr() { return _t.getstr(); }
  @Override public byte isBitShape(Type t) { return _t.isBitShape(t); }
}
