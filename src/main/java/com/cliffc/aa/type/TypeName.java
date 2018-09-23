package com.cliffc.aa.type;

import com.cliffc.aa.AA;

// Named types are essentially a subclass of the named type.
public class TypeName extends Type<TypeName> {
  public  String _name;
  public  Type _t;
  private short _depth;
  private TypeName ( String name, Type t ) { super(TNAME); init(name,t); }
  private void init( String name, Type t ) { assert name!=null; _name=name; _t=t; _depth = (short)(t instanceof TypeName ? ((TypeName)t)._depth+1 : 0); }
  @Override public int hashCode( ) { return TNAME+(_name==null?0:_name.hashCode())+_t.hashCode()+_depth;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeName) ) return false;
    TypeName t2 = (TypeName)o;
    return _t==t2._t && _depth==t2._depth && _name.equals(t2._name);
  }
  @Override public String toString() { return _name+":"+_t; }
  private static TypeName FREE=null;
  @Override protected TypeName free( TypeName f ) { FREE=f; return this; }
  private static TypeName make0( String name, Type t) {
    assert !(t instanceof TypeUnion) || t==TypeUnion.NIL; // No named unions (except nil)
    TypeName t1 = FREE;
    if( t1 == null ) t1 = new TypeName(name,t);
    else { FREE = null; t1.init(name,t); }
    TypeName t2 = (TypeName)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  public static TypeName make( String name, Type t) { return make0(name,t); }

  public  static final TypeName TEST_ENUM = make0("__test_enum",TypeInt.INT8);
  private static final TypeName TEST_FLT  = make0("__test_flt" ,TypeFlt.FLT32);
  private static final TypeName TEST_E2   = make0("__test_e2"  ,TEST_ENUM);
  
  static final TypeName[] TYPES = new TypeName[]{TEST_ENUM,TEST_FLT,TEST_E2};

  @Override protected TypeName xdual() { return new TypeName(_name,_t.dual()); }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    Type mt;
    switch( t._type ) {
    case TERROR:
    case TUNION: return t.xmeet(this); // Let other side decide
    case TNAME:
      TypeName tn = (TypeName)t;
      if( tn._depth > _depth ) return tn.xmeet(this); // Deeper on 'this'
      mt = _t.meet(tn._t);      // Peel name and meet
      if( tn._depth== _depth && _name.equals(tn._name) )
        return make(_name,mt);
      break;                           // Names or depth unequal; treat as unnamed
    default:
      // LHS is named, RHS is unnamed.  If the RHS is high, can keep the name.
      mt = _t.meet(t);
      if( t.above_center() ) return make(_name,mt);
      if( !mt.is_con() ) return mt;
      break;
    }
    // Must fall to the least-upper-bound - which is below the centerline (all
    // constants).  i.e., must fall below any constant; mixing in a null
    // generally works.
    if( mt.may_be_nil() ) {     // mixing in a nil will not drop
      if( mt.isa(Type.NUM) ) return mt.meet(TypeInt.BOOL);
      throw AA.unimpl();
    }
    return mt.meet_nil();
  }

  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean may_be_con() { return _t.may_be_con(); }
  @Override public boolean is_con()   { return _t.is_con(); }
  @Override public boolean may_be_nil() { return _t.may_be_nil(); }
  @Override public boolean may_have_nil() { return _t.may_have_nil(); }
  @Override public double getd  () { return _t.getd  (); }
  @Override public long   getl  () { return _t.getl  (); }
  @Override public String getstr() { return _t.getstr(); }
  @Override public byte isBitShape(Type t) { return _t.isBitShape(t); }
}
