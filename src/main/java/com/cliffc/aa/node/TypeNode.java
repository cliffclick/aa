package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;

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
  @Override String xstr() { return ":"+_t; }
  @Override public Node ideal(GVNGCM gvn) {
    Node arg= in(1);
    Type t = gvn.type(arg);
    if( t.isa(_t) ) return arg;
    // Push TypeNodes 'up' to widen the space they apply to, and hopefully push
    // the type check closer to the source of a conflict.
    if( arg instanceof PhiNode ) {
      Node region = arg.in(0);
      assert region instanceof RegionNode;
      // Cannot change the "shape" of function nodes with potential unknown
      // callers, as the future callers need to see the same arguments.
      if( !(region instanceof FunNode) ) {
        Node nphi = arg.copy(gvn);
        nphi.add_def(region);
        for( int i=1; i<arg._defs._len; i++ )
          nphi.add_def(gvn.xform(new TypeNode(_t,arg.in(i),_error_parse)));
        return nphi;
      }
    }
    
    return null;
  }
  // If the input isa the expected value, we can return it.  Otherwise the
  // TypeNode is "in error", and the program is not type-correct.  Return the
  // asserted value for later code to assume "all is good", but this error here
  // will eventually have to correct (or the program will be rejected).
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(1));
    // Return my input type "pinched" between _t and _t.dual()
    if( _t.dual().isa(t) && t.isa(_t) ) return t;
    return t.above_center() ? _t.dual() : _t;
  }
  @Override public Type all_type() { return _t; }
  @Override public String err(GVNGCM gvn) {
    return _error_parse.typerr(gvn.type(in(1)),_t);
  }    
}
