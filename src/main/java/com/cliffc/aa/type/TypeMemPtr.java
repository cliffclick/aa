package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeObjs.
public final class TypeMemPtr extends Type<TypeMemPtr> {
  // List of known memory aliases.  Zero is nil.
  public BitsAlias _aliases;

  private TypeMemPtr(BitsAlias aliases ) { super     (TMEMPTR); init(aliases); }
  private void init (BitsAlias aliases ) { super.init(TMEMPTR); _aliases = aliases; }
  @Override int compute_hash() {
    return TMEMPTR + _aliases._hash;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr tf = (TypeMemPtr)o;
    return _aliases==tf._aliases;
  }
  //@Override public boolean cycle_equals( Type o ) {
  //  if( this==o ) return true;
  //  if( !(o instanceof TypeMemPtr) ) return false;
  //  TypeMemPtr t2 = (TypeMemPtr)o;
  //  if( _aliases != t2._aliases ) return false;
  //  return true;
  //}
  @Override String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    SB sb = new SB().p('*');
    _aliases.toString(sb);
    if( _aliases.test(0) ) sb.p('?');
    return sb.toString();
  }
  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    sb.p('*');
    _aliases.toString(sb);
    return sb;
  }

  private static TypeMemPtr FREE=null;
  @Override protected TypeMemPtr free( TypeMemPtr ret ) { FREE=this; return ret; }
  public static TypeMemPtr make(BitsAlias aliases ) {
    // Canonical form: cannot have a pointer with only NIL allowed... instead
    // we only use NIL directly.
    assert aliases != BitsAlias.NIL;

    TypeMemPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeMemPtr(aliases);
    else { FREE = null;          t1.init(aliases); }
    TypeMemPtr t2 = (TypeMemPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeMemPtr make( int alias ) { return make(BitsAlias.make0(alias)); }
  public static TypeMemPtr make_nil( int alias ) { return make(BitsAlias.make0(alias).meet_nil()); }

  // Cannot have a NIL here, because a CastNode (JOIN) of a NIL to a "*[4]obj?"
  // yields a TypeMemPtr.NIL instead of a Type.NIL which confuses all ISA tests
  // with embedded NILs.
  //public  static final TypeMemPtr NIL    = (TypeMemPtr)(new TypeMemPtr(BitsAlias.NIL, TypeObj.XOBJ).hashcons());
  public  static final TypeMemPtr OOP0   = make(BitsAlias.FULL    ); // Includes nil
  public  static final TypeMemPtr OOP    = make(BitsAlias.NZERO   );// Excludes nil
  public  static final TypeMemPtr STRPTR = make(BitsAlias.STRBITS );
  public  static final TypeMemPtr STR0   = make(BitsAlias.STRBITS0);
  public  static final TypeMemPtr ABCPTR = make(BitsAlias.ABCBITS );
  public  static final TypeMemPtr ABC0   = make(BitsAlias.ABCBITS0);
          static final TypeMemPtr STRUCT = make(BitsAlias.RECBITS );
  public  static final TypeMemPtr STRUCT0= make(BitsAlias.RECBITS0);
  private static final TypeMemPtr PNTPTR = make(BitsAlias.RECBITS );
  private static final TypeMemPtr PNT0   = make(BitsAlias.RECBITS0);
  static final TypeMemPtr[] TYPES = new TypeMemPtr[]{OOP0,STR0,STRPTR,ABCPTR,STRUCT,ABC0,PNTPTR,PNT0};

  @Override protected TypeMemPtr xdual() {
    if( _aliases==BitsAlias.NIL ) return this;
    return new TypeMemPtr(_aliases.dual());
  }
  @Override TypeMemPtr rdual() {
    if( _dual != null ) return _dual;
    TypeMemPtr dual = _dual = new TypeMemPtr(_aliases.dual());
    dual._dual = this;
    dual._hash = dual.compute_hash();
    dual._cyclic = true;
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TMEMPTR:break;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TRPC:   return cross_nil(t);
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    case TOBJ:
    case TSTR:
    case TSTRUCT:
    case TTUPLE:
    case TFUN:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    // Meet of aliases
    TypeMemPtr ptr = (TypeMemPtr)t;
    BitsAlias aliases = _aliases.meet(ptr._aliases);
    if( aliases == BitsAlias.NIL ) return NIL;
    return make(aliases);
  }
  @Override public boolean above_center() { return _aliases.above_center(); }
  // Aliases represent *classes* of pointers and are thus never constants.
  // nil is a constant.
  @Override public boolean may_be_con()   { return may_nil(); }
  @Override public boolean is_con()       { return _aliases==BitsAlias.NIL; } // only nil
  @Override public boolean must_nil() { return _aliases.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _aliases.may_nil(); }
  @Override Type not_nil() {
    BitsAlias bits = _aliases.not_nil();
    return bits==_aliases ? this : make(bits);
  }
  @Override public Type meet_nil() {
    if( _aliases.test(0) )      // Already has a nil?
      return _aliases.above_center() ? NIL : this;
    BitsAlias aliases = _aliases.meet_nil();
    return aliases==BitsAlias.NIL ? NIL : make(aliases);
  }

  //// Build a depth-limited named type
  //@Override TypeMemPtr make_recur(TypeName tn, int d, VBitSet bs ) {
  //  Type t2 = _obj.make_recur(tn,d,bs);
  //  return t2==_obj ? this : make(_aliases,(TypeObj)t2);
  //}
  // Mark if part of a cycle
  //@Override void mark_cycle( Type head, VBitSet visit, BitSet cycle ) {
  //  if( visit.tset(_uid) ) return;
  //  if( this==head ) { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
  //  _obj.mark_cycle(head,visit,cycle);
  //  if( cycle.get(_obj._uid) )
  //    { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
  //}

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  public byte isBitShape(Type t) {
    return (byte)(t instanceof TypeMemPtr ? 0 : -99);  // Mixing TMP and a non-ptr
  }
  //@SuppressWarnings("unchecked")
  //@Override void walk( Predicate<Type> p ) { if( p.test(this) ) _obj.walk(p); }
  //@Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) { return _cyclic ? _obj.repeats_in_cycles(head,bs) : null; }
  public int getbit() { return _aliases.getbit(); }
  // Keep the high parts
  @Override public TypeMemPtr startype() {
    return TypeMemPtr.make(_aliases.above_center() ? _aliases : _aliases.dual());
  }
}
