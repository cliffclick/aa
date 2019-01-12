package com.cliffc.aa.type;

import com.cliffc.aa.AA;

import java.util.BitSet;

// All Generic Nullable Oops, including Strings, Structs, Tuples, Arrays.
// Excludes nil; to add a nil wrap with TypeNil.
public class TypeOop<O extends TypeOop<O>> extends Type<O> {
  boolean _any;                 // True=choice/join; False=all/meet
  protected   TypeOop(byte type, boolean any) { super(type); init(type,any); }
  protected void init(byte type, boolean any) { assert _type==type; _any=any; }
  @Override public int hashCode( ) { return super.hashCode()+(_any?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeOop && _any==((TypeOop)o)._any;
  }
  @Override String str( BitSet dups) { return _any ? "~oop" : "oop"; }
  private static TypeOop FREE=null;
  @Override protected O free( O ret ) { FREE=this; return ret; }
  public static TypeOop make( boolean any ) {
    TypeOop t1 = FREE;
    if( t1 == null ) t1 = new TypeOop(TOOP,any);
    else { FREE = null; t1.init(TOOP,any); }
    TypeOop t2 = (TypeOop)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static final TypeOop  OOP = make(false); //  OOP
  static final TypeOop XOOP = make(true ); // ~OOP
  static final TypeOop[] TYPES = new TypeOop[]{OOP,XOOP};

  @Override O xdual() { assert _type==TOOP; return (O)new TypeOop(TOOP,!_any); }
      
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    switch( t._type ) {
    case TOOP:
    case TSTRUCT:
    case TTUPLE:
    case TSTR:
      break;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TFUN:
    case TRPC:   return t.must_nil() ? SCALAR : NSCALR;
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    if( this==OOP || t==OOP ) return OOP;
    return t;
  }

  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con() { return _any; }
  @Override public boolean is_con() { return false; }
  @Override boolean must_nil() { return false; }
  @Override Type not_nil(Type ignore) { return this; }
  @Override public Type meet_nil() {
    if( above_center() ) throw com.cliffc.aa.AA.unimpl();
    return TypeNil.make(this);
  }
  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Str); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Str.
  //  0 requires no/free conversion (Str->Str)
  // +1 requires a bit-changing conversion; no auto-unboxing
  // 99 Bottom; No free converts; e.g. Flt->Str requires explicit rounding
  @Override public byte isBitShape(Type t) { throw AA.unimpl();  }
  // Make a (posssibly cyclic & infinite) named type.  Prevent the infinite
  // unrolling of names by not allowing a named-type with depth >= D from
  // holding (recursively) the head of a named-type cycle.  We need to cap the
  // unroll, to prevent loops/recursion from infinitely unrolling.
  @Override Type make_recur(TypeName tn, int d, BitSet bs ) { return this; }
}
