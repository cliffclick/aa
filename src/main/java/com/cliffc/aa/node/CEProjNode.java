package com.cliffc.aa.node;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeTuple;

import static com.cliffc.aa.AA.DSP_IDX;

// Call-graph *edges*.  Always unique (so no hash-consing).  Individually
// turned on or off according to which functions reach a Call or Scope.
public class CEProjNode extends CProjNode {
  public CEProjNode( Node call ) { super(call); }
  public CEProjNode( RootNode root, int fidx ) { super(root,fidx); }
  @Override public String label() { return "CEProj"; }

  @Override public Type value() {
    if( nUses()<1 ) return Type.CTRL; // Dead
    assert !(in(0) instanceof ScopeNode);
    if( in(0).isCopy(0) != null ) return Type.CTRL;
    if( isKeep() ) return Type.CTRL;
    // Expect a call here
    return Type.XCTRL.oob(good_call(val(0),(FunNode)use0()));
  }

  // Never equal to another CEProj, since Call-Graph *edges* are unique
  @Override public boolean equals(Object o) { return this==o; }

  static boolean good_call(Type tcall0, FunNode fun ) {
    if( !(tcall0 instanceof TypeTuple tcall) ) return tcall0!=Type.ANY; // ANY is XCTRL, all other is CTRL
    // Call type tuple
    if( CallNode.tctl(tcall)!=Type.CTRL ) return false; // Call not executing
    TypeFunPtr tfp = CallNode.ttfp(tcall);
    if( tfp.fidxs().above_center() ) return false; // Call not executing yet
    if( !tfp.fidxs().test_recur(fun._fidx) ) return false; // Call not executing this wired path
    // Argument count mismatch
    return tcall.len()-1/*tfp*/ == fun.nargs();
  }

  static boolean wired_arg_check( Type tcall0, FunNode fun ) {
    if( !good_call(tcall0,fun) ) return false;
    TypeTuple tcall = (TypeTuple)tcall0;
    // Check that args are monotonic before wiring
    Node[] parms = fun.parms();
    for( int i=DSP_IDX; i<parms.length; i++ ) {
      if( parms[i]==null ) continue; // Unused args always good
      Type actual = CallNode.targ(tcall,i);
      Type formal = ((ParmNode)parms[i])._t;
      if( !actual.isa(formal) ) return false;
    }
    return true;
  }
}
