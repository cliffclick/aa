package com.cliffc.aa.type;

import com.cliffc.aa.AA;

import java.util.BitSet;

// Types which extend memory-based objects - currently Structs (which include
// tuples but not TypeTuple) and Str (Strings); will include Arrays at some
// point.  Structs have memory words addressed by a base-pointer and a field
// name (for tuples, the field number), and Arrays have memory words addressed
// by a base-pointer and an index.
public class TypeObj<O extends TypeObj<O>> extends Type<O> {
  boolean _any;                 // True=choice/join; False=all/meet
  TypeObj(byte type, boolean any) { super(type); init(type,any); }
  protected void init (byte type, boolean any) { super.init(type); _any=any; }
  @Override public int hashCode( ) { return super.hashCode()+(_any?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeObj && _any==((TypeObj)o)._any && _type==((TypeObj)o)._type;
  }
  @Override String str( BitSet dups ) { return _any?"~obj":"obj"; }
  private static TypeObj make( boolean any ) {
    return (TypeObj)(new TypeObj(TOBJ,any).hashcons());
  }
  static final TypeObj OBJ = make(false);
  static final TypeObj[] TYPES = new TypeObj[]{OBJ};
  
  @Override protected O xdual() { return (O)new TypeObj(TOBJ,!_any); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TNAME: return t.meet(this);
    case TOBJ:  case TSTR:  case TSTRUCT: 
      return _any ? t : this;
    default: return ALL;
    }
  }  
  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con() { return _any; }
  @Override public boolean is_con() { return false; }
}
