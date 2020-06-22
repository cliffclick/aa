package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;
import java.util.HashMap;

// Strings.  Just an alternative TypeObj to TypeStruct - but basically really
// should be replaced with a named Array.
public class TypeStr extends TypeObj<TypeStr> {
  private String _con;          //
  private TypeStr  (String name, boolean any, String con ) { super(TSTR,name,any); init(name,any,con); }
  private void init(String name, boolean any, String con ) {
    super.init(TSTR,name,any);
    _con = con;
  }
  @Override int compute_hash() { return super.compute_hash() + (_con==null ? 0 : _con.hashCode());  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStr) || !super.equals(o) ) return false;
    return Util.eq(_con,((TypeStr)o)._con);
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups) {
    SB sb = new SB();
    if( _any ) sb.p('~');
    if( _con == null ) sb.p("str");
    else sb.p('"').p(_con).p('"');
    return sb.toString();
  }
  private static TypeStr FREE=null;
  @Override protected TypeStr free( TypeStr ret ) { FREE=this; return ret; }
  public static TypeStr make( boolean any, String con ) { return make("",any,con); }
  public static TypeStr make( String name, boolean any, String con ) {
    if( con!=null ) any = false; // "any" is ignored for constants
    TypeStr t1 = FREE;
    if( t1 == null ) t1 = new TypeStr(name,any,con);
    else {   FREE = null;     t1.init(name,any,con); }
    TypeStr t2 = (TypeStr)t1.hashcons();
    if( t1!=t2 ) return t1.free(t2);
    return t1;
  }
  public static TypeStr con(String con) { return make(false,con); }
  public static void init() {} // Used to force class init

  public  static final TypeStr  STR = make(false,null); // not null
  public  static final TypeStr XSTR = make(true ,null); // choice string
  public  static final TypeStr  ABC = make(false,"abc"); // a string constant
  public  static final TypeStr NO_DISP=make(false,"no_disp"); // a string constant
  private static final TypeStr  DEF = con("def"); // a string constant
  static final TypeStr[] TYPES = new TypeStr[]{STR,XSTR,ABC,DEF};
  static void init1( HashMap<String,Type> types ) { types.put("str",STR); }
  // Return a String from a TypeStr constant; assert otherwise.
  @Override public String getstr() { assert _con!=null; return _con; }

  @Override protected TypeStr xdual() { return _con==null ? new TypeStr(_name,!_any,null) : this; }
  @Override TypeStr rdual() {
    if( _dual != null ) return _dual;
    TypeStr dual = _dual = xdual();
    dual._dual = this;
    dual._hash = dual.compute_hash();
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TSTR:   break;
    case TLIVE:
    case TSTRUCT:return OBJ;
    case TOBJ:   return t.above_center() ? this : t;
    case TFUNSIG:
    case TTUPLE:
    case TFUNPTR:
    case TMEMPTR:
    case TFLT:
    case TINT:
    case TRPC:
    case TMEM:   return ALL;
    default: throw typerr(t);
    }
    if( this== STR || t == STR ) return STR;
    if( this==XSTR ) return t   ;
    if( t   ==XSTR ) return this;
    TypeStr ts = (TypeStr)t;
    String con = null;
    if( _any && ts._con != null ) con = ts._con;
    if( ts._any && _con != null ) con =    _con;
    if( Util.eq(_con,ts._con) ) con = _con;
    return make(_any&ts._any,con);
  }

  // Update (approximately) the current TypeObj.  Strings are not allowed to be
  // updated, so this is a program type-error.
  @Override public TypeObj update(byte fin, String fld, Type val) { return STR; }
  @Override public TypeObj st    (byte fin, String fld, Type val) { return STR; }
  @Override public boolean may_be_con() { return super.may_be_con() || _con != null; }
  @Override public boolean is_con() { return _con != null; }
  @Override public Type meet_nil(Type t) { return this; }
  // Widen (loss info), to make it suitable as the default function memory.
  @Override public TypeObj crush() { return this==XSTR ? STR : this; }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Str); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Str.
  //  0 requires no/free conversion (Str->Str)
  // +1 requires a bit-changing conversion; no auto-unboxing
  // 99 Bottom; No free converts; e.g. Flt->Str requires explicit rounding
  @Override public byte isBitShape(Type t) {
    if( t._type==TNIL || t._type==Type.TSTR || t._type == TOBJ ) return 0;
    return 99;
  }
  @Override public Type widen() { return STR; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
