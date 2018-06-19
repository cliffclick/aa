package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() {
    if( at(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj_"+_idx;
  }
  @Override public Node ideal(GVNGCM gvn) { return at(0).is_copy(gvn,_idx); }
  @Override public Type all_type() { return Type.CTRL; }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }
}
