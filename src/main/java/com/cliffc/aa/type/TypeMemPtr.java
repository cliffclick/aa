package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import java.util.BitSet;
import java.util.function.Predicate;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeMems. 
public final class TypeMemPtr extends Type<TypeMemPtr> {

  // A set of TypeOops...

  

  private TypeMemPtr(BitsAlias aliases ) { super     (TMEMPTR); init(aliases); }
  private void init (BitsAlias aliases ) { super.init(TMEMPTR); _aliases = aliases; }
  @Override int compute_hash() { return TMEMPTR + _aliases._hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr tf = (TypeMemPtr)o;
    return _aliases==tf._aliases;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    return "*"+_aliases;
  }

  private static TypeMemPtr FREE=null;
  @Override protected TypeMemPtr free( TypeMemPtr ret ) { FREE=this; return ret; }
  public static TypeMemPtr make( BitsAlias aliases ) {
    TypeMemPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeMemPtr(aliases);
    else { FREE = null;          t1.init(aliases); }
    TypeMemPtr t2 = (TypeMemPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static TypeMemPtr make_nil( TypeOop oop ) {
    throw com.cliffc.aa.AA.unimpl();
  }
  
  public static final TypeMemPtr OOP0   = make(BitsAlias.FULL); // Includes nil
  public static final TypeMemPtr OOP    = make(BitsAlias.NZERO);// Excludes nil
  public static final TypeMemPtr STRPTR = make(TypeStr.STR_alias);
         static final TypeMemPtr STR0   = make_nil(TypeStr.STR_alias);
         static final TypeMemPtr ABCPTR = make(TypeStr.ABC_alias);
  public static final TypeMemPtr ABC0   = make_nil(TypeStr.ABC_alias);
  public static final TypeMemPtr STRUCT = make(TypeStruct.ALLSTRUCT);
  public static final TypeMemPtr STRUCT0= make_nil(TypeStruct.ALLSTRUCT);
  static final TypeMemPtr[] TYPES = new TypeMemPtr[]{OOP0,STRPTR,ABCPTR,STRUCT,ABC0};
  
  @Override protected TypeMemPtr xdual() { return new TypeMemPtr(_aliases.dual()); }
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
    return make(_aliases.meet( ((TypeMemPtr)t)._aliases ));
  }
  public int get_alias() { return _aliases.getbit(); }
  @Override public boolean above_center() { return _aliases.above_center(); }
  // Aliases represent *classes* of pointers and are thus never constants
  @Override public boolean may_be_con()   { return false; }
  @Override public boolean is_con()       { return _aliases.is_con() && _aliases.getbit()==0; }
  @Override public boolean must_nil() { return _aliases.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _aliases.may_nil(); }
  @Override Type not_nil() {
    // Below center, return this; above center remove nil choice
    return above_center() && _aliases.test(0) ? make(_aliases.clear(0)) : this;
  }
  @Override public Type meet_nil() {
    if( _aliases.test(0) )      // Already has a nil?
      return _aliases.above_center() ? TypeNil.NIL : this;
    return make(_aliases.meet(BitsAlias.NIL));
  }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
