package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Allocates a TypeStr in memory.  Weirdly takes a string OBJECT (not pointer),
// and produces the pointer.  Hence liveness is odd.
//
// NewStrNode produces a Tuple type, with the TypeStr and a TypeMemPtr.
public class NewStrNode extends NewNode<TypeStr> {
  public NewStrNode( TypeStr ts, Node str ) {
    super(OP_NEWSTR,BitsAlias.STR,ts,str);
  }
  @Override public Type value(GVNGCM gvn) {
    TypeObj newt=TypeObj.UNUSED; // If dead
    if( !is_unused() ) {
      // Gather args and produce a TypeStruct
      Type xs = gvn.type(fld(0));
      newt = xs instanceof TypeStr ? (TypeStr)xs : (TypeStr)xs.oob(TypeStr.STR);
    }
    return TypeTuple.make(newt,_tptr); // Complex obj, simple ptr.
  }
  @Override TypeStr dead_type() { return TypeStr.XSTR; }
  // The one string field is memory-alive
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return TypeMem.ANYMEM; }
}
