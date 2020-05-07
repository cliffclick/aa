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
    TypeMem defmem = (TypeMem)gvn.type(Env.DEFMEM);
    if( defmem == TypeMem.UNUSED ) return TypeMem.UNUSED; // Shortcut
    TypeObj[] objs = defmem.alias2objs();
    for( int i=objs.length-1; i>=0; i-- )
      if( objs[i]==TypeObj.UNUSED ) { // Find last unused
        TypeObj[] tos = new TypeObj[i+1];
        tos[1] = TypeObj.XOBJ;  // Default is XOBJ, not UNUSED
        for( int j=2; j<=i; j++ )
          if( objs[j]==TypeObj.UNUSED )
            tos[j] = TypeObj.UNUSED;
        return TypeMem.make0(tos);
      }
    return TypeMem.EMPTY;
  }
  // StartMemNodes are never equal
  @Override public int hashCode() { return 123456789+2; }
  @Override public boolean equals(Object o) { return this==o; }
  @Override public Type all_type() { return TypeMem.ISUSED; }
}
