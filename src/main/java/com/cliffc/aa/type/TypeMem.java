package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.BitSet;

// Memory type; the state of all of memory; memory edges order memory ops.
// Produced at the program start, consumed by all function calls, consumed be
// Loads, consumed and produced by Stores.  Can be broken out in the
// "equivalence class" model of memory over a bulk memory to allow more fine
// grained knowledge.
public class TypeMem extends Type<TypeMem> {
  // Get a unique new alias#, used to group chunks of memory together - 
  // such that Loads and Stores approximate in the same alias chunk.
  private static int ALIAS=1;   // Unique alias number, skipping 0
  public static int new_alias() { return ALIAS++; }
  // Mapping from alias#s to the current known alias state
  private final Ary<TypeOop> _aliases;
  private TypeMem( ) { super(TMEM); _aliases = new Ary<>(new TypeOop[0]); init(); }
  private void init( ) {  }
  @Override public int hashCode( ) { return _aliases.hashCode() + TMEM; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    if( _aliases._len != tf._aliases._len ) return false;
    for( int i=0; i<_aliases._len; i++ )
      if( _aliases._es[i] != tf._aliases._es[i] )
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups ) {
    SB sb = new SB().p("{");
    for( int i=0; i<_aliases._len; i++ )
      if( _aliases._es[i] != null )
        sb.p(i).p(":").p(_aliases._es[i].toString()).p("'");
    return sb.p("}").toString();
  }
  
  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases.clear(); FREE=this; return ret; }
  private static TypeMem make( ) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem();
    else { FREE = null; t1.init(); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeMem make(int alias, TypeOop oop ) {
    TypeMem mem = make();
    mem._aliases.setX(alias,oop);
    return mem;
  }

  public static final TypeMem MEM_EMPTY = make();
  public static final TypeMem MEM_STR = make(TypeStr.STR_alias,TypeStr.STR);
  static final TypeMem[] TYPES = new TypeMem[]{MEM_EMPTY,MEM_STR};
  
  @Override protected TypeMem xdual() { return this; }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TMEM: break;
    default:   return ALL; // 
    }
    TypeMem tf = (TypeMem)t;
    throw com.cliffc.aa.AA.unimpl();
  }
  
  @Override public boolean above_center() { return false; }
  @Override public boolean may_be_con()   { return false; }
  @Override public boolean is_con()       { return false; }
  @Override boolean must_nil() { return false; } // never a nil
  @Override Type not_nil(Type ignore) { return this; }
}
