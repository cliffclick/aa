package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Down-cast.  Used to e.g., throw away read-write privilege and become
// read-only hereafter.
public class MeetNode extends Node {
  public final Type _t;
  public MeetNode( Node val, Type t ) { super(OP_MEET,null,val); _t=t; }
  @Override String xstr() { return "&"+_t; }
  @Override public Node ideal(GVNGCM gvn) { return null;  }
  @Override public Type value(GVNGCM gvn) { return _t.meet(gvn.type(in(1))); }
}
