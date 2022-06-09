package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeTuple;

import static com.cliffc.aa.AA.DSP_IDX;

// Call-graph *edges*.  Always unique (so no hash-consing).  Individually
// turned on or off according to which functions reach a Call or Scope.
public class CEProjNode extends CProjNode {
  public CEProjNode( Node call ) { super(call); }
  @Override public String xstr() { return "CEProj"; }

  @Override public Type value() {
    if( _uses._len<1 ) return Type.CTRL; // Dead
    assert !(in(0) instanceof ScopeNode);
    if( in(0).is_copy(0) != null ) return Type.CTRL;
    if( is_keep() ) return Type.CTRL;
    // Expect a call here
    return good_call(val(0),(FunNode)_uses.at(0)) ? Type.CTRL : Type.XCTRL;
  }

  // Never equal to another CEProj, since Call-Graph *edges* are unique
  @Override public boolean equals(Object o) { return this==o; }

  static boolean good_call(Type tcall, FunNode fun ) {
    if( !(tcall instanceof TypeTuple ttcall) ) return !tcall.above_center();
    // Call type tuple
    if( ttcall.at(0)!=Type.CTRL ) return false; // Call not executing
    TypeFunPtr tfp = CallNode.ttfp(ttcall);
    if( tfp.fidxs().above_center() ) return false; // Call not executing yet
    if( !tfp.fidxs().test_recur(fun._fidx) )
      return false;             // Call not executing this wired path
    // Argument count mismatch
    return ttcall.len()-1/*tfp*//*-1 tesc turned off*/ == fun.nargs();
  }

  static boolean wired_arg_check( Type tcall, FunNode fun ) {
    if( !good_call(tcall,fun) ) return false;
    // Check that args are monotonic before wiring
    Node[] parms = fun.parms();
    for( int i=DSP_IDX; i<parms.length; i++ ) {
      if( parms[i]==null ) continue; // Unused args always good
      Type actual = CallNode.targ(tcall,i);
      Type formal = ((ParmNode)parms[i])._t;
      if( !actual.isa(formal) )
        return false;
    }
    return true;
  }
}
