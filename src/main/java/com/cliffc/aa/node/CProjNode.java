package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn, int idx ) { this(OP_CPROJ,ifn,idx); }
  public CProjNode( byte op, Node ifn, int idx ) { super(op,ifn,idx); }
  @Override String xstr() {
    if( !is_dead() && in(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj"+_idx;
  }
  @Override public Type value(byte opt_mode) {
    Type x = super.value(opt_mode);
    if( x==Type.ANY ) return Type.XCTRL;
    if( x==Type.ALL ) return Type. CTRL;
    return x;
  }
  @Override public TypeMem live_use( byte opt_mode, Node def ) { return def.basic_liveness() ? TypeMem.ALIVE : TypeMem.ANYMEM; }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }

}
