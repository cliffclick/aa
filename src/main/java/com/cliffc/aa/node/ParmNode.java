package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  public final int _idx;    // Parameter index, zero-based; -1 reserved for RPC
  final String _name;       // Parameter name
  public ParmNode( int idx, String name, FunNode fun, ConNode defalt, String badgc) {
    super(OP_PARM,fun,defalt,badgc);
    _idx=idx;
    _name=name;
  }
  @Override String xstr() { return "Parm:"+_name; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode) ) return false;
    ParmNode parm = (ParmNode)o;
    return _idx==parm._idx;
  }
  @Override public Type value( GVNGCM gvn ) {
    FunNode fun = (FunNode) in(0);
    assert fun._defs._len==_defs._len;
    if( fun._cidx != 0 ) return gvn.type(in(fun._cidx)); // Region has collapsed to a Copy, no need to run full merge
    Type t = _default_type.dual();
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(fun.in(i))!=Type.XCTRL ) { // Only meet alive paths
        Type argt = gvn.type(in(i));   // Arg type for this incoming path
        if( _idx < 0 || argt.isa(fun._tf.arg(_idx)) ) // Argument is legal?  Illegal args are not merged, and error-reported in CallNode
          t = t.meet(argt);
      }
    return t;
  }
}
