package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Allocates a TypeStr in memory.
//
// NewStrNode produces a Tuple type, with the TypeStr and a TypeMemPtr.
public class NewStrNode extends NewNode<TypeStr> {
  public NewStrNode( TypeStr ts, Node mem, Node str ) {
    super(OP_NEWSTR,BitsAlias.STR,ts,mem,str);
  }
  @Override public Type value(GVNGCM gvn) {
    Type tmem0 = gvn.type(mem());
    if( !(tmem0 instanceof TypeMem) ) return tmem0.oob();
    TypeMem tmem = (TypeMem)tmem0;
    TypeObj newt=TypeObj.UNUSED; // If dead
    if( _ts!=dead_type() ) {
      // Gather args and produce a TypeStruct
      Type xs = gvn.type(fld(0));
      newt = xs instanceof TypeStr ? (TypeStr)xs : (TypeStr)xs.oob(TypeStr.STR);
    }
    TypeMem tmem2 = !escaped(gvn) // No escape on pointer, so no incoming self-variant
      ? tmem.set(_alias,newt)    // Stomp over incoming value at same alias
      : tmem.st (_alias,newt);   // Merge with incoming value at same alias
    return TypeTuple.make(tmem2,_tptr); // Complex obj, simple ptr.
  }
  @Override TypeStr dead_type() { return TypeStr.XSTR; }
}
