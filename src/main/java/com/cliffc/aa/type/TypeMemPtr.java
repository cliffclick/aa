package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;

import java.util.BitSet;
import java.util.function.Predicate;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeObjs.  
public final class TypeMemPtr extends Type<TypeMemPtr> {
  // List of known memory aliases.  Zero is nil.
  BitsAlias _aliases;
  public TypeObj _obj;          // Meet/join of aliases
  
  private TypeMemPtr(BitsAlias aliases, TypeObj obj ) { super     (TMEMPTR); init(aliases,obj); }
  private void init (BitsAlias aliases, TypeObj obj ) { super.init(TMEMPTR); _aliases = aliases; _obj=obj; }
  @Override int compute_hash() { return TMEMPTR + _aliases._hash + _obj._hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr tf = (TypeMemPtr)o;
    return _aliases==tf._aliases && _obj==tf._obj;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    if( dups == null ) dups = new BitSet();
    else if( dups.get(_uid) ) return "*"; // Break recursive printing cycle
    dups.set(_uid);
    SB sb = new SB().p('*');
    _aliases.toString(sb).p(_obj.str(dups));
    if( _aliases.test(0) ) sb.p('?');
    return sb.toString();
  }

  private static TypeMemPtr FREE=null;
  @Override protected TypeMemPtr free( TypeMemPtr ret ) { FREE=this; return ret; }
  public static TypeMemPtr make(BitsAlias aliases, TypeObj obj ) {
    TypeMemPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeMemPtr(aliases,obj);
    else { FREE = null;          t1.init(aliases,obj); }
    TypeMemPtr t2 = (TypeMemPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeMemPtr make    ( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias)           ,obj); }
         static TypeMemPtr make_nil( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias).meet_nil(),obj); }
  public        TypeMemPtr make    (            TypeObj obj ) { return make(_aliases,obj); }
  
  public static final TypeMemPtr OOP0   = make(BitsAlias.FULL    , TypeObj.OBJ); // Includes nil
  public static final TypeMemPtr OOP    = make(BitsAlias.NZERO   , TypeObj.OBJ);// Excludes nil
  public static final TypeMemPtr STRPTR = make(BitsAlias.STRBITS , TypeStr.STR);
         static final TypeMemPtr STR0   = make(BitsAlias.STRBITS0, TypeStr.STR);
  public static final TypeMemPtr ABCPTR = make(BitsAlias.ABCBITS , TypeStr.ABC);
  public static final TypeMemPtr ABC0   = make(BitsAlias.ABCBITS0, TypeStr.ABC);
  public static final TypeMemPtr STRUCT = make(BitsAlias.RECBITS , TypeStruct.ALLSTRUCT);
         static final TypeMemPtr STRUCT0= make(BitsAlias.RECBITS0, TypeStruct.ALLSTRUCT);
  static final TypeMemPtr[] TYPES = new TypeMemPtr[]{OOP0,STRPTR,ABCPTR,STRUCT,ABC0};
  
  @Override protected TypeMemPtr xdual() { return new TypeMemPtr(_aliases.dual(),(TypeObj)_obj.dual()); }
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
    return make(_aliases.meet(ptr._aliases), (TypeObj)_obj.meet(ptr._obj));
  }
  @Override public boolean above_center() { return _aliases.above_center(); }
  // Aliases represent *classes* of pointers and are thus never constants.
  // nil is a constant.
  @Override public boolean may_be_con()   { return may_nil(); }
  @Override public boolean is_con()       { return !_aliases.is_class(); } // only nil
  @Override public boolean must_nil() { return _aliases.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _aliases.may_nil(); }
  @Override Type not_nil() {
    BitsAlias bits = _aliases.not_nil();
    return bits==_aliases ? this : make(bits,_obj);
  }
  @Override public Type meet_nil() {
    if( _aliases.test(0) )      // Already has a nil?
      return _aliases.above_center() ? TypeNil.NIL : this;
    return make(_aliases.meet_nil(),_obj);
  }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
  public int getbit() { return _aliases.getbit(); }
}
