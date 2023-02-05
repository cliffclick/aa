package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.BitsFun;

// Control from the Root.  Computes value from escaped FIDXS.
public class CRProjNode extends CEProjNode {
  public CRProjNode( int fidx ) { super(Env.ROOT,fidx); assert fidx!=0; }
  @Override public String xstr() { return "CRProj["+_idx+"]"; }
  private RootNode root() { return (RootNode)in(0); }
  @Override public Type value() {
    // Malformed or during reset
    if( len()==0 ) return Type.CTRL;
    // Not done parsing yet
    if( root().in(0)==null ) return Type.CTRL;
    if( is_prim() ) return Type.CTRL; // Primitives never die
    // Before Combo runs, calls might yet wire.  The default path cannot die
    // until wiring is done.
    if( AA.LIFTING && !Combo.HM_FREEZE ) return Type.CTRL;
    // During or Post-Combo, compute liveness from Root value
    BitsFun rfidxs = root().rfidxs();
    if( rfidxs.above_center() ) return Type.XCTRL;
    // On or off, according to if the fidx escaped.
    return Type.XCTRL.oob(rfidxs.test_recur(_idx));
  }
}
