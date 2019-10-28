package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;
import java.util.function.Predicate;

// Strings.  Just an alternative TypeObj to TypeStruct - but basically really
// should be replaced with a named Array.
public class TypeStr extends TypeObj<TypeStr> {
  private String _con;          //
  private TypeStr  (boolean any, String con, BitsAlias news ) { super(TSTR,any, news); init(any,con,news); }
  private void init(boolean any, String con, BitsAlias news ) {
    super.init(TSTR,any,news);
    _con = con;
  }
  @Override int compute_hash() { return super.compute_hash() + (_con==null ? 0 : _con.hashCode());  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStr) ) return false;
    TypeStr t2 = (TypeStr)o;
    return _any == t2._any && (_con==null ? t2._con==null : _con.equals(t2._con));
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
  public static TypeStr make( boolean any, String con, BitsAlias news ) {
    if( con!=null ) any = false; // "any" is ignored for constants
    TypeStr t1 = FREE;
    if( t1 == null ) t1 = new TypeStr(any,con,news);
    else { FREE = null; t1.init(any,con,news); }
    TypeStr t2 = (TypeStr)t1.hashcons();
    if( t1!=t2 ) return t1.free(t2);
    // Constant strings are made with a null _news, so they can hash-cons to
    // each other - they are all made pre-compilation and exist in the original
    // program image.  If we decide to keep the constant, we'll give it a
    // unique alias.
    if( t1._news==null ) {
      assert t1._con != null;
      t1._news = BitsAlias.make0(BitsAlias.new_alias(BitsAlias.STR));
    }
    return t1;
  }
  @Override public TypeStr make( boolean any, BitsAlias news ) { return make(any,_con,news); }
  public static TypeStr con(String con) { return make(false,con,null); }
  public static void init() {} // Used to force class init

  // Get the alias for string constants.  Since string constants are interned,
  // so are the aliases.
  //public int get_alias() { return _news.getbit(); }
  
  public  static final TypeStr  STR = make(false,null,BitsAlias.STRBITS); // not null
  public  static final TypeStr XSTR = make(true ,null,BitsAlias.STRBITS); // choice string
  public  static final TypeStr  ABC = make(false,"abc",BitsAlias.ABCBITS); // a string constant
  private static final TypeStr  DEF = con("def"); // a string constant
  static final TypeStr[] TYPES = new TypeStr[]{STR,XSTR,ABC,DEF};
  static void init1( HashMap<String,Type> types ) { types.put("str",STR); }
  // Return a String from a TypeStr constant; assert otherwise.
  @Override public String getstr() { assert is_con(); return _con; }

  @Override protected TypeStr xdual() { return _con==null ? new TypeStr(!_any,_con,_news.dual()) : this; }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TSTR:     break;
    case TNAME:  return t.xmeet(this); // Let other side decide
    case TSTRUCT:return OBJ;
    case TOBJ:   return t.above_center() ? this : t;
    case TNIL:
    case TTUPLE: 
    case TFUNPTR:
    case TMEMPTR:
    case TFLT:
    case TINT:
    case TFUN:
    case TRPC:
    case TMEM:   return ALL;
    default: throw typerr(t);
    }
    if( this== STR || t == STR ) return STR;
    if( this==XSTR ) return t   ;
    if( t   ==XSTR ) return this;
    assert _con!=null && ((TypeStr)t)._con!=null;
    return _con.equals(((TypeStr)t)._con) ? con(_con) : STR;
  }

  // Update (approximately) the current TypeObj.  Strings are not allowed to be
  // updated, so this is a program type-error.
  @Override public TypeObj update(byte fin, String fld, int fld_num, Type val) { return STR; }
  @Override public TypeObj st    (byte fin, String fld, int fld_num, Type val) { return STR; }
  @Override BitsAlias aliases() { return BitsAlias.STRBITS; }
  @Override public TypeObj lift_final() { return this; }
  @Override public boolean may_be_con() { return super.may_be_con() || _con != null; }
  @Override public boolean is_con() { return _con!=null; }
  @Override public Type meet_nil() { return this; }
  
  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Str); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Str.
  //  0 requires no/free conversion (Str->Str)
  // +1 requires a bit-changing conversion; no auto-unboxing
  // 99 Bottom; No free converts; e.g. Flt->Str requires explicit rounding
  @Override public byte isBitShape(Type t) {
    if( t._type==TNIL || t._type==Type.TSTR ) return 0;
    return 99;
  }
  @Override public Type widen() { return STR; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
  // Flip low to high
  @Override public TypeObj startype() { return this==STR ? XSTR : this; }
}
