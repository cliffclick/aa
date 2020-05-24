package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Program memory start
public class StartMemNode extends Node {
  public StartMemNode(StartNode st, DefMemNode def) { super(OP_STMEM,st,def); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    // All memories are XOBJ, unless UNUSED in the default memory.
    Type defmem = gvn.type(Env.DEFMEM);
    if( !(defmem instanceof TypeMem) ) return defmem.oob();
    if( defmem == TypeMem.ANYMEM ) return TypeMem.ANYMEM; // Shortcut
    TypeObj[] objs = ((TypeMem)defmem).alias2objs().clone();
    for( int i=1; i<objs.length; i++ )
      if( objs[i]!=null && objs[i]!=TypeObj.UNUSED )
        objs[i]=TypeObj.XOBJ;
    return TypeMem.make0(objs);
  }
  // StartMemNodes are never equal
  @Override public int hashCode() { return 123456789+2; }
  @Override public boolean equals(Object o) { return this==o; }
}
