package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;

import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Predicate;

public class TypeStr extends TypeOop<TypeStr> {
  private String _con;          // 
  private TypeStr  (boolean any, String con ) { super(TSTR,any); init(any,con); }
  private void init(boolean any, String con ) {
    super.init(TSTR,any);
    _con = con;
  }
  @Override public int hashCode( ) { return super.hashCode()+(_con==null ? 0 : _con.hashCode());  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStr) ) return false;
    TypeStr t2 = (TypeStr)o;
    return _any == t2._any && (_con==null ? t2._con==null : _con.equals(t2._con));
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    SB sb = new SB();
    if( _any ) sb.p('~');
    if( _con == null ) sb.p("str");
    else sb.p('"').p(_con).p('"');
    return sb.toString();
  }
  private static TypeStr FREE=null;
  @Override protected TypeStr free( TypeStr ret ) { FREE=this; return ret; }
  public static TypeStr make( boolean any, String con ) {
    assert con==null || !any;
    TypeStr t1 = FREE;
    if( t1 == null ) t1 = new TypeStr(any,con);
    else { FREE = null; t1.init(any,con); }
    TypeStr t2 = (TypeStr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeStr con(String con) { return make(false,con); }

  public  static final TypeStr  STR = make(false,null); // not null
  public  static final TypeStr XSTR = make(true ,null); // choice string
  public  static final TypeStr  ABC = con("abc"); // a string constant
  private static final TypeStr  DEF = con("def"); // a string constant
  static final TypeStr[] TYPES = new TypeStr[]{STR,XSTR,ABC,DEF};
  static void init1( HashMap<String,Type> types ) { types.put("str",STR); }
  // Return a String from a TypeStr constant; assert otherwise.
  @Override public String getstr() { assert is_con(); return _con; }

  @Override protected TypeStr xdual() { return new TypeStr(!_any,_con); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TSTR:   break;
    case TSTRUCT:
    case TTUPLE: return OOP;
    case TFUNPTR:
    case TFLT:
    case TINT:
    case TFUN:
    case TRPC:   return t.must_nil() ? SCALAR : NSCALR;
    case TOOP:
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    if( this== STR || t == STR ) return STR;
    if( this==XSTR ) return t   ;
    if( t   ==XSTR ) return this;
    assert _con!=null && ((TypeStr)t)._con!=null;
    return _con.equals(((TypeStr)t)._con) ? con(_con) : STR;
  }

  @Override public boolean may_be_con() { return super.may_be_con() || _con != null; }
  @Override public boolean is_con() { return _con!=null; }
  @Override public Type meet_nil() {
    return above_center() ? TypeNil.STR : TypeNil.make(this);
  }
  
  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Str); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Str.
  //  0 requires no/free conversion (Str->Str)
  // +1 requires a bit-changing conversion; no auto-unboxing
  // 99 Bottom; No free converts; e.g. Flt->Str requires explicit rounding
  @Override public byte isBitShape(Type t) {
    if( t._type==TNIL || t._type==Type.TSTR || t._type==Type.TOOP || t._type==Type.TSCALAR ) return 0;
    return 99;
  }
  @Override public Type widen() { return STR; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
