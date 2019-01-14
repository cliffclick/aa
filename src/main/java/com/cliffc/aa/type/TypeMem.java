package com.cliffc.aa.type;

import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

import java.util.BitSet;

// Memory type; the state of all of memory; memory edges order memory ops.
// Produced at the program start, consumed by all function calls, consumed be
// Loads, consumed and produced by Stores.  Can be broken out in the
// "equivalence class" model of memory over a bulk memory to allow more fine
// grained knowledge.
public class TypeMem extends Type<TypeMem> {

  private TypeMem( ) { super(TMEM); init(); }
  private void init( ) { }
  @Override public int hashCode( ) { return TMEM;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    return "Mem";
  }
  
  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { FREE=this; return ret; }
  public static TypeMem make( ) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem();
    else { FREE = null; t1.init(); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static final TypeMem MEM = make();
  static final TypeMem[] TYPES = new TypeMem[]{MEM};
  
  @Override protected TypeMem xdual() { return this; }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TMEM: break;
    default:   return ALL; // 
    }
    TypeMem tf = (TypeMem)t;
    return make();
  }
  
  @Override public boolean above_center() { return false; }
  @Override public boolean may_be_con()   { return false; }
  @Override public boolean is_con()       { return false; }
  @Override boolean must_nil() { return false; } // never a nil
  @Override Type not_nil(Type ignore) { return this; }
}
