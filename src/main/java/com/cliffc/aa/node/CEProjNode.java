package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj control
public class CEProjNode extends CProjNode {
  final TypeFunSig _sig;
  public CEProjNode( CallNode call, TypeFunSig sig ) { super(call); _sig = sig; }
  @Override public String xstr() { return "CEProj"; }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( _uses._len<1 ) return Type.CTRL;
    return good_call(val(0),_uses.at(0)) ? Type.CTRL : Type.XCTRL;
  }
  // Never equal to another CEProj, since Call-Graph *edges* are unique
  @Override public int hashCode() { return super.hashCode()+(_sig==null ? 0 : _sig._hash); }
  @Override public boolean equals(Object o) { return this==o; }

  static boolean good_call(Type tcall, Node ftun ) {
    if( !(tcall instanceof TypeTuple) ) return !tcall.above_center();
    TypeTuple ctup = (TypeTuple)tcall; // Call type tuple
    if( ctup.at(0)!=Type.CTRL ) return false; // Call not executing
    if( ftun instanceof ThunkNode ) return true; // Thunk call is OK by design
    FunNode fun = (FunNode)ftun;
    if( fun._thunk_rhs ) return true; // Thunk call is OK by design
    TypeFunPtr tfp = CallNode.ttfp(ctup);
    if( tfp.fidxs().above_center() ) return false; // Call not executing yet
    if( !tfp.fidxs().test_recur(fun._fidx) )
      return false;             // Call not executing this wired path

    //// Argument count mismatch
    //TypeTuple formals = fun._sig._formals;
    //if( ctup.len()-2 != formals.len() ) return false;
    //// Check good args
    //TypeMem tmem = (TypeMem)ctup.at(AA.MEM_IDX);
    //for( int i=AA.MEM_IDX; i<formals.len(); i++ ) {
    //  Type formal = formals.at(i);
    //  Type actual0= ctup.at(i);
    //  if( actual0==Type.ANY && formal==Type.ALL ) continue; // Allow ignored error args
    //  // If any argument (or display, fidx, memory) is high, do not enable the
    //  // CFG edge.  Wait until all args are sane (allowing XNIL as sane).
    //  if( actual0.above_center() && actual0!=Type.XNIL ) return false;
    //  Type actual = tmem.sharptr(actual0);
    //  // See if all args might lift to some valid formal.  Must be monotonic,
    //  // and any high args is already False.  So all args are at/below center.
    //  // "(actual.JOIN.formal is below_center)" may be agood arg.
    //  Type join   = actual.join(formal);
    //  if( join.above_center() && join!=Type.XNIL )
    //    return false;
    //}
    return true;
  }
}
