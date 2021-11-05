package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeTuple;

// Call-graph *edges*.  Always unique (so no hash-consing).  Individually
// turned on or off according to which functions reach a Call or Scope.
public class CEProjNode extends CProjNode {
  public CEProjNode( Node call ) { super(call); }
  @Override public String xstr() { return "CEProj"; }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( _uses._len<1 ) return Type.CTRL; // Dead
    assert !(in(0) instanceof ScopeNode);
    if( in(0).is_copy(0) != null ) return Type.CTRL;
    // Expect a call here
    return good_call(val(0),_uses.at(0)) ? Type.CTRL : Type.XCTRL;
  }

  // Never equal to another CEProj, since Call-Graph *edges* are unique
  @Override public boolean equals(Object o) { return this==o; }

  static boolean good_call(Type tcall, Node ftun ) {
    if( !(tcall instanceof TypeTuple) ) return !tcall.above_center();
    TypeTuple ttcall = (TypeTuple)tcall; // Call type tuple
    if( ttcall.at(0)!=Type.CTRL ) return false; // Call not executing
    if( ftun instanceof ThunkNode ) return true; // Thunk call is OK by design
    FunNode fun = (FunNode)ftun;
    if( fun._thunk_rhs ) return true; // Thunk call is OK by design
    TypeFunPtr tfp = CallNode.ttfp(ttcall);
    if( tfp.fidxs().above_center() ) return false; // Call not executing yet
    if( !tfp.fidxs().test_recur(fun._fidx) )
      return false;             // Call not executing this wired path

    // Cannot use the obvious argument check "actual.isa(formal)"!!!!!

    // If the actual is higher than formal (not even above_center), but then
    // falls during Opto, this type would LIFT from Ctrl to XCTRL.  Can only
    // test for static properties (e.g. argument count, or constant ALL
    // arguments).

    // Argument count mismatch
    return ttcall.len()-1/*tfp*/-1/*esc*/ == fun.formals().nargs();
  }

  @Override public TV2 new_tvar( String alloc_site) { return null; }
}
