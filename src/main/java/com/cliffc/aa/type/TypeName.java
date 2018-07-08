package com.cliffc.aa.type;

public class TypeName extends Type {
  public  String _name;
  public  Type _t;
  private int _depth;
  private TypeName ( String name, Type t ) { super(TNAME); init(name,t); }
  private void init( String name, Type t ) { _name=name; _t=t; _depth = t instanceof TypeName ? ((TypeName)t)._depth+1 : 0; }
  @Override public int hashCode( ) { return TNAME+_name.hashCode()+_t.hashCode()+_depth;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeName) ) return false;
    TypeName t2 = (TypeName)o;
    return _t==t2._t && _depth == t2._depth && _name.equals(t2._name);
  }
  @Override public String toString() { return _name+":"+_t; }
  private static TypeName FREE=null;
  private TypeName free( TypeName f ) { FREE=f; return this; }
  public static TypeName make( String name, Type t) {
    TypeName t1 = FREE;
    if( t1 == null ) t1 = new TypeName(name,t);
    else { FREE = null; t1.init(name,t); }
    TypeName t2 = (TypeName)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static private final TypeName TEST_ENUM = make("__test_enum",TypeInt.INT8);
  static private final TypeName TEST_FLT  = make("__test_flt" ,TypeFlt.FLT32);
  static private final TypeName TEST_E2   = make("__test_e2"  ,TEST_ENUM);
  
  static final TypeName[] TYPES = new TypeName[]{TEST_ENUM,TEST_FLT,TEST_E2};

  @Override protected TypeName xdual() { return _t==_t.dual() ? this : new TypeName(_name,_t.dual()); }
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    switch( t._type ) {
    case TNAME:
      TypeName tn = (TypeName)t;
      if( tn._depth > _depth ) return tn.xmeet(this); // Deeper on 'this'
      if( tn._depth== _depth ) {
        Type mt = _t.meet(tn._t);
        return _name.equals(tn._name) ? make(_name,mt) : mt;
      }
      break;
    case TUNION: return t.xmeet(this); // Let TypeUnion decide
    case TERROR: return ((TypeErr)t)._all ? t : this;
    default: break;
    }
    // LHS is named, RHS is unnamed.  Only keep the name if RHS is above
    // center, since that is "all names".
    Type mt = _t.meet(t);       // Peel and meet
    return t.above_center() && mt==_t ? this : mt;
  }


  @Override public double getd  () { return _t.getd  (); }
  @Override public long   getl  () { return _t.getl  (); }
  @Override public String getstr() { return _t.getstr(); }
  @Override public byte isBitShape(Type t) { return _t.isBitShape(t); }
  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean canBeConst() { return _t.canBeConst(); }
  @Override public boolean is_con()   { return _t.is_con(); }
}
