package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.Arrays;
import java.util.BitSet;

// Memory type; the state of all of memory; memory edges order memory ops.
// Produced at the program start, consumed by all function calls, consumed be
// Loads, consumed and produced by Stores.  Can be broken out in the "equiv-
// alence class" (Alias#) model of memory over a bulk memory to allow more fine
// grained knowledge.  Memory is accessed via Alias#s, where all TypeObjs in an
// Alias class are Meet together as an approximation.
public class TypeMem extends Type<TypeMem> {
  // Mapping from alias#s to the current known alias state
  private TypeObj[] _aliases;
  // The "default" infinite mapping.  Everything past _aliases.length or null
  // maps to the default instead.  If the default is null, then the aliasing is
  // exact, and trying to read null is an error.
  private TypeObj _def;
  
  private TypeMem  (TypeObj def, TypeObj[] aliases ) { super(TMEM); init(def,aliases); }
  private void init(TypeObj def, TypeObj[] aliases ) {
    super.init(TMEM);
    _def = def;
    _aliases = aliases;
    assert check(def,aliases);
  }
  // "tight": no extra instances of default
  private static boolean check(TypeObj def, TypeObj[] aliases ) {
    if( def != null )
      for( TypeObj obj : aliases )
        if( obj==def )
          return false; // Extra instances of default; messes up canonical rep for hash-cons
    return aliases.length==0 || aliases[aliases.length-1] != def;
  }
  @Override public int hashCode( ) {
    return super.hashCode() +
      (_aliases==null ? 0 : Arrays.hashCode(_aliases)) +
      (_def==null ? 0 : _def.hashCode());
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    if( _def != tf._def || _aliases.length != tf._aliases.length ) return false;
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != tf._aliases[i] ) // note '==' and NOT '.equals()'
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups ) {
    SB sb = new SB();
    sb.p("{");
    if( _def != null )
      sb.p("mem:").p(_def.toString()).p(",");
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        sb.p(i).p(":").p(_aliases[i].toString()).p(",");
    return sb.p("}").toString();
  }
  // Alias must exist
  TypeObj at(int alias) {
    TypeObj rez = at0(alias);
    assert rez != null : "Fetching alias "+alias+" which does not exist";
    return rez;
  }
  private TypeObj at0(int alias) {
    if( alias >= _aliases.length ) return _def;
    TypeObj obj = _aliases[alias];
    return obj==null ? _def : obj;
  }
  
  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases=null; FREE=this; return ret; }
  static TypeMem make( TypeObj def, TypeObj[] aliases ) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem(def,aliases);
    else { FREE = null;       t1.init(def,aliases); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Precise single alias
  public static TypeMem make(int alias, TypeObj oop ) {
    assert oop!=null;
    TypeObj[] oops = new TypeObj[alias+1];
    oops[alias] = oop;
    return make(null,oops);
  }

  public  static final TypeMem MEM = make(TypeStruct.ALLSTRUCT,new TypeObj[0]);
  public  static final TypeMem MEM_STR = make(TypeStr.STR_alias,TypeStr.STR);
  public  static final TypeMem MEM_ABC = make(TypeStr.ABC_alias,TypeStr.ABC);
  static final TypeMem[] TYPES = new TypeMem[]{MEM,MEM_STR};

  // All mapped memories remain, but each memory flips internally.
  @Override protected TypeMem xdual() {
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = (TypeObj)_aliases[i].dual();
    return new TypeMem(_def==null ? null : (TypeObj)_def.dual(), oops);
  }
  @Override protected Type xmeet( Type t ) {
    if( t._type != TMEM ) return ALL; //
    TypeMem tf = (TypeMem)t;
    // Meet of default values, meet of element-by-element.
    // If either default is null, take the other.
    TypeObj def = _def==null ? tf._def : (tf._def==null ? _def : (TypeObj)_def.meet(tf._def));
    int len = Math.max(_aliases.length,tf._aliases.length);
    TypeObj[] objs = new TypeObj[len];
    for( int i=0; i<len; i++ ) {
      TypeObj o0 =    at0(i);
      TypeObj o1 = tf.at0(i);
      TypeObj obj = o0==null ? o1 : (o1==null ? o0 : (TypeObj)o0.meet(o1));
      if( obj == def ) obj = null;
      objs[i] = obj;
    }
    // Remove elements redundant with the default value
    while( len > 0 && objs[len-1]==null ) len--;
    if( len < objs.length ) objs = Arrays.copyOf(objs,len);
    return make(def,objs);
  }

  // Meet of all possible loadable values
  public TypeObj ld( TypeMemPtr ptr ) {
    boolean any = ptr.above_center();
    TypeObj obj = TypeObj.OBJ;
    if( !any ) obj = (TypeObj)TypeObj.OBJ.dual();
    for( int alias : ptr._aliases ) {
      TypeObj x = at(alias);
      obj = (TypeObj)(any ? obj.join(x) : obj.meet(x));
    }
    return obj;
  }
  
  @Override public boolean above_center() { return false; }
  @Override public boolean may_be_con()   { throw com.cliffc.aa.AA.unimpl();}
  @Override public boolean is_con()       { throw com.cliffc.aa.AA.unimpl();}
  @Override boolean must_nil() { return false; } // never a nil
  @Override Type not_nil() { return this; }
}
