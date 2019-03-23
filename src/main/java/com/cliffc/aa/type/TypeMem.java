package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.Arrays;
import java.util.BitSet;

// Memory type; the state of all of memory; memory edges order memory ops.
// Produced at the program start, consumed by all function calls, consumed be
// Loads, consumed and produced by Stores.  Can be broken out in the
// "equivalence class" model of memory over a bulk memory to allow more fine
// grained knowledge.
public class TypeMem extends TypeAnyAll<TypeMem> {
  // Mapping from alias#s to the current known alias state
  private Type[] _aliases;
  // The "default" infinite mapping.  Everything past _aliases.length maps to
  // the default instead.  If the default is ALL, then the aliasing is exact,
  // and trying to read ALL is an error.
  private Type _def;
  
  private TypeMem  (boolean any, Type def, Type[] aliases ) { super(TMEM,any); init(any,def,aliases); }
  private void init(boolean any, Type def, Type[] aliases ) {
    super.init(TMEM,any);
    assert check(def,aliases);
    _def = def;
    _aliases = aliases;
  }
  // "tight": no trailing instances of default
  private static boolean check(Type def, Type[] aliases ) {
    return aliases.length==0 || aliases[aliases.length-1] != def;
  }
  @Override public int hashCode( ) { return super.hashCode() + Arrays.hashCode(_aliases) + _def.hashCode(); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    if( _any != tf._any || _def != tf._def || _aliases.length != tf._aliases.length ) return false;
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != tf._aliases[i] ) // note '==' and NOT '.equals()'
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups ) {
    SB sb = new SB();
    if( _any ) sb.p('~');
    sb.p("{");
    if( _def != ALL )
      sb.p("mem:").p(_def.toString()).p(",");
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != _def )
        sb.p(i).p(":").p(_aliases[i].toString()).p(",");
    return sb.p("}").toString();
  }
  Type at(int alias) {
    Type rez = alias >= _aliases.length ? _def : _aliases[alias];
    assert rez != _def : "Fetching alias "+alias+" which does not exist";
    return rez;
  }
  private Type at0(int alias) {
    return alias >= _aliases.length ? _def : _aliases[alias];
  }
  
  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases=null; FREE=this; return ret; }
  private static TypeMem make( boolean any, Type def, Type[] aliases ) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem(any,def,aliases);
    else { FREE = null;       t1.init(any,def,aliases); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeMem make(int alias, Type oop ) {
    assert oop!=null;
    Type[] oops = new Type[alias+1];
    Arrays.fill(oops,ALL);
    oops[alias] = oop;
    return make(false,ALL,oops);
  }

  public  static final TypeMem MEM = make(false,TypeStruct.ALLSTRUCT,new Type[0]);
  private static final TypeMem MEM_STR = make(TypeStr.STR_alias,TypeStr.STR);
  static final TypeMem[] TYPES = new TypeMem[]{MEM,MEM_STR};

  // All mapped memories remain, but each memory flips internally.
  @Override protected TypeMem xdual() {
    Type[] oops = new Type[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = _aliases[i].dual();
    return new TypeMem(!_any,_def.dual(), oops);
  }
  @Override protected Type xmeet( Type t ) {
    if( t._type != TMEM ) return ALL; //
    TypeMem tf = (TypeMem)t;
    // Meet of default values, meet of element-by-element
    Type def = _def.meet(tf._def);
    int len = Math.max(_aliases.length,tf._aliases.length);
    Type[] oops = new Type[len];
    for( int i=0; i<len; i++ )
      oops[i] = at0(i).meet(tf.at0(i));
    // Remove elements redundant with the default value
    while( len > 0 && oops[len-1]==def ) len--;
    if( len < oops.length ) oops = Arrays.copyOf(oops,len);
    return make(_any&tf._any,def,oops);
  }

  // Meet of all possible aliases
  public Type meets( TypeMemPtr ptr ) {
    throw com.cliffc.aa.AA.unimpl();
  }

  
  @Override public boolean above_center() { return false; }
  @Override public boolean may_be_con()   { return false; }
  @Override public boolean is_con()       { return false; }
  @Override boolean must_nil() { return false; } // never a nil
  @Override Type not_nil(Type ignore) { return this; }
}
