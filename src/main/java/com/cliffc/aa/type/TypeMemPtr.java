package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

import java.util.BitSet;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeMems. 
public final class TypeMemPtr extends TypeAnyAll<TypeMemPtr> {
  // List of known memory aliases
  private Bits _aliases;

  private TypeMemPtr(boolean any, Bits aliases ) { super     (TMEMPTR,any); init(any,aliases); }
  private void init (boolean any, Bits aliases ) { super.init(TMEMPTR,any); _aliases = aliases; }
  @Override public int hashCode( ) { return TMEMPTR + _aliases.hashCode();  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr tf = (TypeMemPtr)o;
    return _any==tf._any && _aliases==tf._aliases;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    SB sb = new SB();
    if( _any ) sb.p('~');
    sb.p('*').p(_aliases.toString());
    return sb.toString();
  }

  private static TypeMemPtr FREE=null;
  @Override protected TypeMemPtr free( TypeMemPtr ret ) { FREE=this; return ret; }
  public static TypeMemPtr make( int alias ) { return make(false, Bits.make(alias)); }
  public static TypeMemPtr make( boolean any, Bits aliases ) {
    TypeMemPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeMemPtr(any,aliases);
    else { FREE = null;          t1.init(any,aliases); }
    TypeMemPtr t2 = (TypeMemPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static final TypeMemPtr  MEMPTR = make(false,Bits.FULL);
         static final TypeMemPtr  STRPTR = make(TypeStr.STR_alias);
         static final TypeMemPtr  ABCPTR = make(TypeStr.ABC_alias);
  static final TypeMemPtr[] TYPES = new TypeMemPtr[]{MEMPTR,STRPTR,ABCPTR};
  
  @Override protected TypeMemPtr xdual() { return new TypeMemPtr(!_any,_aliases.dual()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TMEMPTR:break;
    case TFLT:
    case TINT:
    case TSTR:
    case TFUNPTR:
    case TRPC:   return t.must_nil() ? SCALAR : NSCALR;
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    case TSTRUCT:
    case TTUPLE:
    case TFUN:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    // Join of args; meet of aliases
    TypeMemPtr ptr = (TypeMemPtr)t;
    Bits aliases = _aliases.meet( ptr._aliases );
    return make(_any&ptr._any,aliases);
  }

  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con()   { return _any || _aliases.is_con(); }
  @Override public boolean is_con()       { return false; }
  @Override boolean must_nil() { return false; }
  @Override Type not_nil(Type ignore) { return this; }
  @Override public Type meet_nil() { return TypeNil.make(this); }
  public int alias() { return _aliases.getbit(); }
}
