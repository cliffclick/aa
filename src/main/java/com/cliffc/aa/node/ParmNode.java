package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  final int _idx;    // Parameter index, zero-based; -1 reserved for RPC
  private final String _name;       // Parameter name
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
  @Override public Node ideal(GVNGCM gvn) {
    FunNode fun = (FunNode) in(0);
    assert fun._defs._len==_defs._len;
    if( gvn.type(fun) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    return fun._defs.len() == 2 && gvn.type(fun)==Type.XCTRL ? in(1) : null; // Fun has collapsed to a Copy, fold up
  }
  // Unlike the default value() call, this call does NOT accumulate errors from
  // dead input paths.
  @Override public Type value( GVNGCM gvn ) {
    FunNode fun = (FunNode) in(0);
    assert fun._defs._len==_defs._len;
    // For the function being returned-at-top, and thus NOT called on this path
    // - ignore the argument check.  Function is not being called.
    Type t = _default_type.dual();
    if( _defs._len==2 && fun._returned_at_top )
      return t; // Never called, so no argument fails
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type_ne(fun.in(i))!=Type.XCTRL ) { // Only meet alive paths
        Type argt = gvn.type(in(i));    // Arg type for this incoming path
        Type arg_ne = argt instanceof TypeErr ? ((TypeErr)argt)._t : argt;
        // Unlike PhiNode.value, also add in argument errors.
        if( _idx >= 0 && !arg_ne.isa(fun._tf.arg(_idx)) ) // Argument is legal?
          throw com.cliffc.aa.AA.unimpl();
        t = t.meet(argt);
      }
    return t;
  }
}
