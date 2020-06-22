package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Allocates a TypeStr in memory.
//
// NewStrNode produces a Tuple type, with the TypeStr and a TypeMemPtr.
public class NewStrNode extends NewNode<TypeStr> {
  public NewStrNode( TypeStr ts, Node ctrl, Node str ) {
    super(OP_NEWSTR,BitsAlias.STR,ts,ctrl);
    add_def(str);
  }
  @Override public Type value(GVNGCM gvn) {
    // Gather args and produce a TypeStruct
    Type xs = gvn.type(fld(0));
    TypeStr ss = xs instanceof TypeStr ? (TypeStr)xs : (TypeStr)xs.oob(TypeStr.STR);
    return TypeTuple.make(ss,TypeMemPtr.make(_alias,TypeObj.OBJ));
  }
  @Override TypeStr dead_type() { return TypeStr.XSTR; }
}
