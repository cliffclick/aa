package com.cliffc.aa.type;

import com.cliffc.aa.AA;

import java.util.BitSet;

// Types which support an any/all notion, including Strings, Structs, Arrays,
// Tuples, MemPtrs, Mem.  Excludes nil; to add a nil wrap with TypeNil.  This
// class is not part of the Type heirarchy, but instead is a structural
// convenience.
public abstract class TypeAnyAll<O extends TypeAnyAll<O>> extends Type<O> {
  boolean _any;                 // True=choice/join; False=all/meet
  protected TypeAnyAll(byte type, boolean any) { super(type); init(type,any); }
  protected void init (byte type, boolean any) { super.init(type); _any=any; }
  @Override public int hashCode( ) { return super.hashCode()+(_any?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeAnyAll && _any==((TypeAnyAll)o)._any && _type==((TypeAnyAll)o)._type;
  }
  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con() { return _any; }
  @Override public boolean is_con() { return false; }
}
