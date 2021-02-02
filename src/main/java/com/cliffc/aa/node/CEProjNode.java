package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj control
public class CEProjNode extends CProjNode {
  public CEProjNode( CallNode call, TypeFunSig sig ) { super(call); _sig = sig; }
  TypeFunSig _sig;
  @Override public String xstr() { return "CEProj"; }
  @Override public Type value(GVNGCM.Mode opt_mode) { return good_call(val(0),_sig,_sig==null) ? Type.CTRL : Type.XCTRL; }
  // Will typically have the same Call input,
  @Override public int hashCode() { return super.hashCode()+(_sig==null ? 0 : _sig._hash); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CEProjNode) ) return false;
    CEProjNode proj = (CEProjNode)o;
    return _sig==proj._sig;
  }

  static boolean good_call(Type tcall, TypeFunSig sig, boolean thunk_rhs) {
    if( !(tcall instanceof TypeTuple) ) return !tcall.above_center();
    TypeTuple ctup = (TypeTuple)tcall; // Call type tuple
    if( sig==null || thunk_rhs ) return true; // Thunk call is OK by design
    // Argument count mismatch
    if( ctup.len()-2 != sig._formals.len() ) return false;
    // Check good args
    TypeMem tmem = (TypeMem)ctup.at(AA.MEM_IDX);
    for( int i=AA.MEM_IDX; i<sig._formals.len(); i++ ) {
      Type formal = sig._formals.at(i);
      Type actual0= ctup.at(i);
      if( actual0==Type.ANY && formal==Type.ALL ) continue; // Allow ignored error args
      // If any argument (or display, fidx, memory) is high, do not enable the
      // CFG edge.  Wait until all args are sane (allowing XNIL as sane).
      if( actual0.above_center() && actual0!=Type.XNIL ) return false;
      Type actual = tmem.sharptr(actual0);
      // See if all args might lift to some valid formal.  Must be monotonic,
      // and any high args is already False.  So all args are at/below center.
      // "(actual.JOIN.formal is below_center)" may be agood arg.
      Type join   = actual.join(formal);
      if( join.above_center() && join!=Type.XNIL )
        return false;
    }
    return true;
  }
}
