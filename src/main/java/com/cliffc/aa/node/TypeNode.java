package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Assert the matching type.  Parse-time error if it does not remove.  Note the
// difference with CastNode: both Nodes always join their input with their
// constant but a TypeNode has to be proven useless and removed before the
// program is type-correct.  A CastNode is always correct from call/return
// semantics, but the join is not-locally-obviously-correct.  The Cast makes it
// locally obvious.
public class TypeNode extends Node {
  final Type _t;                // TypeVar???
  final Parse _error_parse;     // Used for error messages
  public TypeNode( Type t, Node n, Parse P ) { super(OP_TYPE,null,n); _t=t; _error_parse = P; }
  @Override String xstr() { return "@"+_t; }
  @Override public Node ideal(GVNGCM gvn) {
    Node arg=at(1);
    Type t = gvn.type(arg);
    if( t.isa(_t) ) return arg;
    // Push TypeNodes 'up' to widen the space they apply to, and hopefully push
    // the type check closer to the source of a conflict.
    if( arg instanceof PhiNode ) {
      Node region = arg.at(0);
      assert region instanceof RegionNode;
      // Cannot change the "shape" of function nodes with potential unknown
      // callers, as the future callers need to see the same arguments.
      if( !(region instanceof FunNode && ((FunNode)region).has_unknown_callers(gvn)) ) {
        Node nphi = arg.copy();
        nphi.add_def(region);
        for( int i=1; i<arg._defs._len; i++ )
          nphi.add_def(gvn.xform(new TypeNode(_t,arg.at(i),_error_parse)));
        return nphi;
      }
    }
    
    return null;
  }
  @Override public Type value(GVNGCM gvn) { return _t.join(gvn.type(at(1))); }
  @Override public Type all_type() { return _t; }
  String err(GVNGCM gvn) {
    Type t = gvn.type(at(1));
    if( t instanceof TypeErr ) return ((TypeErr)t)._msg;
    String s = t.forward_ref() ? ((TypeFun)t).forward_ref_err() : t.toString()+" is not a "+_t;
    return _error_parse.errMsg(s);
  }
}
