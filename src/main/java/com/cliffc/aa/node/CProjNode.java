package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn ) { this(ifn,AA.CTL_IDX); }
  public CProjNode( Node ifn, int idx ) { super(OP_CPROJ,ifn,idx); }
  @Override public String xstr() {
    if( !is_dead() && in(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj"+_idx;
  }
  @Override boolean is_CFG() { return in(0).is_CFG(); }
  @Override public Type value() {
    if( in(0)._op==OP_ROOT ) return Type.CTRL; // Program Start
    // Normal projection, except pinch to CTRL.
    Type x = super.value();
    if( x==Type.ANY ) return Type.XCTRL;
    if( x==Type.ALL ) return Type. CTRL;
    return x;
  }
  @Override Type live_use( Node def ) { return def.is_mem() ? TypeMem.ANYMEM : Type.ALL; }
}
