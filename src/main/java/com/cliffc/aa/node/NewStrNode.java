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
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.  Since this can happen DURING opto (when a call resolves)
    // and during iter, "freeze" the value in-place.  It will DCE shortly.
    if( _captured )
      return gvn.self_type(this);

    // Gather args and produce a TypeStruct
    Type xs = gvn.type(fld(0));
    if( !(xs instanceof TypeObj) ) return all_type();
    return TypeTuple.make(xs,TypeMemPtr.make(_alias));
  }
}
