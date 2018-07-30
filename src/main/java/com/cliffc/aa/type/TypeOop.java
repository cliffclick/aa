package com.cliffc.aa.type;

import com.cliffc.aa.AA;

// All Generic Nullable Oops, including Strings, Structs, Tuples, Arrays
public class TypeOop extends TypeNullable {
  boolean _any;                 // True=choice/join; False=all/meet
  protected TypeOop ( byte nil, boolean any) { super(TOOP,nil); init(nil,any); }
  protected void init(byte nil, boolean any) { super.init(nil); _any=any; assert _type==TOOP; }
  @Override public int hashCode( ) { return super.hashCode()+(_any?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeOop && eq((TypeOop)o) && _any==((TypeOop)o)._any;
  }
  @Override public String toString() { return (_any?"~":"")+String.format(TSTRS[_nil],"oop"); }
  private static TypeOop FREE=null;
  private TypeOop free( TypeOop f ) { assert f._type==TOOP; FREE=f; return this; }
  public static TypeOop make( byte nil, boolean any ) {
    TypeOop t1 = FREE;
    if( t1 == null ) t1 = new TypeOop(nil,any);
    else { FREE = null; t1.init(nil,any); }
    TypeOop t2 = (TypeOop)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static public final TypeOop OOP0 = make(AND_NIL,false); // OOP&nil
  static public final TypeOop OOP  = make(NOT_NIL,false); // OOP
  static public final TypeOop NIL  = make( IS_NIL,false); // nil
  static public final TypeOop OOP_ = make( OR_NIL, true); // ~OOP+nil
  static final TypeOop[] TYPES = new TypeOop[]{OOP0,OOP,NIL,OOP_};

  @Override protected TypeOop xdual() { return new TypeOop(xdualnil(),!_any); }
      
  @Override protected Type xmeet( Type t ) {
    if( t == this ) return this;
    switch( t._type ) {
    case TOOP:
    case TSTRUCT:
    case TTUPLE:
    case TSTR:
      break;
    case TFLT:
    case TINT:
      //if(   may_be_nil() ) return t.meet(TypeInt.NIL);
      //if( t.may_be_nil() ) return   make_nil();
      //return t._type==TFLT||t._type==TINT ? SCALAR : OOP0;
      throw com.cliffc.aa.AA.unimpl();
    case TRPC:
    case TFUN:   return SCALAR;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TNAME:  
    case TUNION: return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    return _any ? t.meet(this) : make(nmeet((TypeNullable)t),false);
  }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Str); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Str.
  //  0 requires no/free conversion (Str->Str)
  // +1 requires a bit-changing conversion; no auto-unboxing
  // 99 Bottom; No free converts; e.g. Flt->Str requires explicit rounding
  @Override public byte isBitShape(Type t) { throw AA.unimpl();  }
  @Override public boolean above_center() { throw AA.unimpl(); }
  @Override public boolean canBeConst() { throw AA.unimpl(); }
  @Override public boolean is_con()   { throw AA.unimpl(); }
  // True if this OOP may BE a nil (as opposed to: may have a nil)
  public boolean may_be_nil() { throw AA.unimpl(); }
}
