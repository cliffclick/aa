package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  final int _idx;               // Parameter index, zero-based; -1 reserved for RPC
  final String _name;   // Parameter name
  public ParmNode( int idx, String name, FunNode fun, Node defalt, String badgc) { super(OP_PARM,fun,defalt,badgc); _idx=idx; _name=name; }
  @Override String xstr() { return "Parm:"+_name; }
  @Override public Type value(GVNGCM gvn) {
    if( in(0) instanceof FunNode && !((FunNode) in(0)).callers_known(gvn) ) { // Slot zero allows unknown callers
      assert in(0).in(1) instanceof ScopeNode; // Function is visible in current scope, to be looked up
      return gvn.type(in(1)).meet(((ConNode)in(1))._t);   // More unknown callers, assume worst-case input type
    }
    return super.value(gvn);
  }
  @Override public Type all_type() { return in(1) instanceof ConNode ? ((ConNode) in(1))._t : TypeErr.ALL ; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode) ) return false;
    ParmNode parm = (ParmNode)o;
    return _idx==parm._idx;
  }
}
