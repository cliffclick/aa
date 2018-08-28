package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeRPC;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  final int _idx;           // Parameter index, zero-based; -1 reserved for RPC
  final String _name;       // Parameter name
  public ParmNode( int idx, String name, FunNode fun, ConNode defalt, String badgc) {
    super(OP_PARM,fun,defalt,badgc);
    _idx=idx;
    _name=name;
  }
  @Override String xstr() { return "Parm:"+_name; }
  @Override public Type value(GVNGCM gvn) {
    if( _idx==-1 && gvn._opt ) { // If running optimistic, extra RPCs can be found in the FunNode
      Node fun = in(0);
      assert fun._defs._len==_defs._len;
      Type t = TypeRPC.ALL_CALL.dual();
      if( gvn.type(fun.in(1))==Type.CTRL ) { // If slot#1 is alive, count all discovered fun-ptr callers
        TypeRPC trpcs = ((FunNode)in(0))._rpcs;
        if( trpcs != null ) t = trpcs; // Keep fun-ptr callers
      }
      for( int i=2; i<_defs._len; i++ )
        if( gvn.type(fun.in(i))==Type.CTRL ) // Only meet alive paths
          t = t.meet(gvn.type(in(i)));     // Merge in fixed callers
      return t;
    }
    // Otherwise just like a Phi
    return super.value(gvn);
  }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode) ) return false;
    ParmNode parm = (ParmNode)o;
    return _idx==parm._idx;
  }
}
