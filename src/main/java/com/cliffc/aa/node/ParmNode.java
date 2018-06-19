package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  final int _idx;               // Parameter index, zero-based; -1 reserved for RPC
  final String _name;   // Parameter name
  public ParmNode( int idx, String name, FunNode fun, Node defalt) { super(OP_PARM,fun,defalt); _idx=idx; _name=name; }
  @Override String xstr() { return "Parm:"+_name; }
  @Override public Type value(GVNGCM gvn) {
    if( at(0) instanceof FunNode && !((FunNode)at(0)).callers_known(gvn) ) {
      assert at(0).at(1) instanceof ScopeNode;
      assert !gvn.type(at(1)).is_con();
      return gvn.type(at(1));   // More unknown callers, assume worst-case input type
    }
    return super.value(gvn);
  }
  @Override public Type all_type() { return at(1) instanceof ConNode ? ((ConNode)at(1))._t : Type.SCALAR ; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode) ) return false;
    ParmNode parm = (ParmNode)o;
    return _idx==parm._idx;
  }
}
