package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeTuple;

// Control from the Root.  Computes value from escaped FIDXS.
public class CRProjNode extends CEProjNode {
  public CRProjNode( int fidx ) { super(Env.ROOT,fidx); assert fidx!=0; }
  @Override public String xstr() {
    return "CRProj["+_idx+"]";
  }
  @Override public Type value() {
    // Before Combo runs, calls might yet wire.  The default path cannot die
    // until wiring is done.
    if( in(0).in(0)==null ) return Type.CTRL;
    if( is_prim() ) return Type.CTRL; // Primitives never die
    if( val(0)==Type.ANY ) return Type.XCTRL;
    // Compute liveness from Root value
    TypeTuple tt = (TypeTuple)val(0);
    TypeFunPtr tfp = (TypeFunPtr)tt.at(3);
    if( tfp.fidxs().above_center() ) return Type.XCTRL;
    // On or off, according to if the fidx escaped.
    return Type.XCTRL.oob(tfp.test(_idx));
  }
}
