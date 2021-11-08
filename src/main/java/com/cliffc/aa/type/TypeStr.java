package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;
import java.util.function.Predicate;

import static com.cliffc.aa.type.TypeFld.Access;

// Strings.  Just an alternative TypeObj to TypeStruct - but basically really
// should be replaced with a named Array.
public class TypeStr extends TypeObj<TypeStr> {
  private String _con;          //
  private TypeStr init(String name, boolean any, String con ) {
    super.init(name,any,any);
    _con = con;
    return this;
  }
  @Override int compute_hash() { return super.compute_hash() + (_con==null ? 0 : _con.hashCode());  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStr) || !super.equals(o) ) return false;
    return Util.eq(_con,((TypeStr)o)._con);
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( _any ) sb.p('~');
    if( _con == null ) sb.p("str");
    else sb.p('"').p(_con).p('"');
    return sb;
  }

  static { new Pool(TSTR,new TypeStr()); }
  public static TypeStr make( String name, boolean any, String con ) {
    TypeStr t1 = POOLS[TSTR].malloc();
    return t1.init(name,any,con).hashcons_free();
  }

  public static TypeStr make( boolean any, String con ) { return make("",any,con); }
  public static TypeStr con(String con) { return make(false,con); }
  public static void init() {} // Used to force class init

  public  static final TypeStr  STR = make(false,null);  // not null
  public  static final TypeStr XSTR = STR.dual();        // choice string
  public  static final TypeStr  ABC = make(false,"abc"); // a string constant
  private static final TypeStr  DEF = con("def"); // a string constant
  static final TypeStr[] TYPES = new TypeStr[]{STR,ABC,DEF};
  static void init1( HashMap<String,Type> types ) { types.put("str",TypeMemPtr.STRPTR); }
  // Return a String from a TypeStr constant; assert otherwise.
  @Override public String getstr() { assert _con!=null; return _con; }

  @Override protected TypeStr xdual() {
    return _con == null ? POOLS[TSTR].<TypeStr>malloc().init(_name, !_any,_con) : this; }
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
    case TARY:
    case TLIVE:
    case TSTRUCT:return OBJ;
    case TOBJ:   return t.xmeet(this);
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
    TypeStr ts = (TypeStr)t;
    boolean any = _any&ts._any;
    String con = null;
    if( ts._any && ts._con==null ) con =    _con;
    else if( _any &&  _con==null ) con = ts._con;
    else if( Util.eq(_con,ts._con) ) con =  _con;
    else any=false;
    return make("",any,con);
  }

  // Update (approximately) the current TypeObj.  Strings are not allowed to be
  // updated, so this is a program type-error.
  @Override public TypeObj update(Access fin, String fld, Type val) { return this; }

  @Override public boolean may_be_con() { return super.may_be_con() || _con != null; }
  @Override public boolean is_con() { return _con != null; }
  @Override public Type meet_nil(Type t) { return this; }
  // Widen (loss info), to make it suitable as the default function memory.
  @Override public TypeObj crush() { return this; }

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
  @Override public TypeStr  widen() { return STR; }
  @Override public void walk( Predicate<Type> p ) { p.test(this); }

  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) { return BitsFun.EMPTY; }
}
