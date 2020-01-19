package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import java.util.HashMap;
import java.util.function.Predicate;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeObjs.
public final class TypeMemPtr extends Type<TypeMemPtr> {
  // List of known memory aliases.  Zero is nil.
  public BitsAlias _aliases;
  public TypeObj _obj;          // Meet/join of aliases

  private TypeMemPtr(BitsAlias aliases, TypeObj obj ) { super     (TMEMPTR); init(aliases,obj); }
  private void init (BitsAlias aliases, TypeObj obj ) { super.init(TMEMPTR); _aliases = aliases; _obj=obj; }
  @Override int compute_hash() {
    assert _obj._hash != 0;
    return TMEMPTR + _aliases._hash + _obj._hash;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr tf = (TypeMemPtr)o;
    return _aliases==tf._aliases && _obj==tf._obj;
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr t2 = (TypeMemPtr)o;
    if( _aliases != t2._aliases ) return false;
    return _obj == t2._obj || _obj.cycle_equals(t2._obj);
  }
  @Override String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    SB sb = new SB().p('*');
    _aliases.toString(sb).p(_obj.str(dups));
    if( _aliases.test(0) ) sb.p('?');
    return sb.toString();
  }
  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    sb.p('*');
    _obj.dstr(_aliases.toString(sb).p(" -> "),dups);
    return sb;
  }

  private static TypeMemPtr FREE=null;
  @Override protected TypeMemPtr free( TypeMemPtr ret ) { FREE=this; return ret; }
  public static TypeMemPtr make(BitsAlias aliases, TypeObj obj ) {
    // Canonical form: cannot have a pointer with only NIL allowed... instead
    // we only use NIL directly.
    assert aliases != BitsAlias.NIL;
    TypeMemPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeMemPtr(aliases,obj);
    else { FREE = null;          t1.init(aliases,obj); }
    TypeMemPtr t2 = (TypeMemPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeMemPtr make( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias),obj); }
  public static TypeMemPtr make_nil( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias).meet_nil(),obj); }

  public  static final TypeMemPtr OOP0   = make(BitsAlias.FULL    ,TypeObj.OBJ); // Includes nil
  public  static final TypeMemPtr OOP    = make(BitsAlias.NZERO   ,TypeObj.OBJ); // Excludes nil
  public  static final TypeMemPtr STRPTR = make(BitsAlias.STRBITS ,TypeStr.STR);
  public  static final TypeMemPtr STR0   = make(BitsAlias.STRBITS0,TypeStr.STR);
  public  static final TypeMemPtr ABCPTR = make(BitsAlias.type_alias(BitsAlias.STR),TypeStr.ABC);
  public  static final TypeMemPtr ABC0   = (TypeMemPtr)ABCPTR.meet_nil();
  public  static final TypeMemPtr STRUCT = make(BitsAlias.RECBITS ,TypeStruct.ALLSTRUCT);
  public  static final TypeMemPtr STRUCT0= make(BitsAlias.RECBITS0,TypeStruct.ALLSTRUCT);
  static final TypeMemPtr[] TYPES = new TypeMemPtr[]{OOP0,STR0,STRPTR,ABCPTR,STRUCT};

  @Override protected TypeMemPtr xdual() {
    assert _aliases!=BitsAlias.NIL;
    return new TypeMemPtr(_aliases.dual(),(TypeObj)_obj.dual());
  }
  @Override TypeMemPtr rdual() {
    if( _dual != null ) return _dual;
    TypeMemPtr dual = _dual = new TypeMemPtr(_aliases.dual(),(TypeObj)_obj.rdual());
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
    return make(aliases,(TypeObj)_obj.meet(ptr._obj));
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
    return bits==_aliases ? this : make(bits,_obj);
  }
  @Override public Type meet_nil() {
    if( _aliases.test(0) )      // Already has a nil?
      return _aliases.above_center() ? NIL : this;
    BitsAlias aliases = _aliases.meet_nil();
    return aliases==BitsAlias.NIL ? NIL : make(aliases,_obj);
  }

  public BitsAlias aliases() { return _aliases; }

  // Recursively reachable aliases
  public BitsAlias recursive_aliases(BitsAlias abs, TypeMem mem) {
    for( int alias : _aliases )
      if( alias != 0 )
        abs = mem.recursive_aliases(abs,alias);
    return abs;
  }

  // Build a mapping from types to their depth in a shortest-path walk from the
  // root.  Only counts depth on TypeStructs with the matching alias.  Only
  // used for testing.
  HashMap<Type,Integer> depth() {
    int alias = _aliases.getbit();
    HashMap<Type,Integer> ds = new HashMap<>();
    Ary<TypeStruct> t0 = new Ary<>(new TypeStruct[]{(TypeStruct)_obj});
    Ary<TypeStruct> t1 = new Ary<>(new TypeStruct[1],0);
    int d=0;                    // Current depth
    while( !t0.isEmpty() ) {
      while( !t0.isEmpty() ) {
        TypeStruct ts = t0.pop();
        if( ds.putIfAbsent(ts,d) == null )
          for( Type tf : ts._ts ) {
            if( ds.putIfAbsent(tf,d) == null &&  // Everything in ts is in the current depth
                tf instanceof TypeMemPtr ) {
              TypeMemPtr tmp = (TypeMemPtr)tf;
              if( tmp._obj instanceof TypeStruct )
                (tmp._aliases.test(alias) ? t1 : t0).push((TypeStruct)tmp._obj);
            }
          }
      }
      Ary<TypeStruct> tmp = t0; t0 = t1; t1 = tmp; // Swap t0,t1
      d++;                                         // Raise depth
    }
    return ds;
  }

  // Max depth of struct, with a matching alias TMP
  static int max(int alias, HashMap<Type,Integer> ds) {
    int max = -1;
    for( Type t : ds.keySet() )
      if( (t instanceof TypeMemPtr) && ((TypeMemPtr)t)._aliases.test(alias) )
        max = Math.max(max,ds.get(t));
    return max+1;               // Struct is 1 more depth than TMP
  }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  public byte isBitShape(Type t) {
    return (byte)(t instanceof TypeMemPtr ? 0 : -99);  // Mixing TMP and a non-ptr
  }
  @SuppressWarnings("unchecked")
  @Override void walk( Predicate<Type> p ) { if( p.test(this) ) _obj.walk(p); }
  public int getbit() { return _aliases.getbit(); }
  // Keep the high parts
  @Override public TypeMemPtr startype() {
    return TypeMemPtr.make(_aliases.above_center() ? _aliases : _aliases.dual(), _obj.startype());
  }
}
