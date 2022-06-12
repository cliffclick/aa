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
    if( val(0)==Type.ANY ) return Type.XCTRL;
    // Compute liveness from Root value
    TypeTuple tt = (TypeTuple)val(0);
    TypeFunPtr tfp = (TypeFunPtr)tt.at(0);
    // On or off, according to if the fidx escaped.
    return Type.XCTRL.oob(tfp._fidxs.test_recur(_idx));
  }
}
