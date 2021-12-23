package com.cliffc.aa.node;

import com.cliffc.aa.type.Type;

// ValNodes behave like FunPtrNodes in some contexts (can be called; acts like
// a constructor), and like a Memory in other contexts (can be loaded through
// like a pointer).  Marker interface to help keep uses correct.
public abstract class ValFunNode extends Node {
  ValFunNode(byte op, Node... defs) { super(op,defs); }
  abstract int nargs();
  // The *declared* argument type, not analyzed type
  abstract Type argtype(int idx);
  // The actual value, as a TypeFunPtr (or OOB).
  // For ValNodes, it is the constructor signature.
  abstract Type funtype();
}
