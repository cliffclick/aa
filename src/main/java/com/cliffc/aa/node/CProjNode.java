package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeNil;
import com.cliffc.aa.type.TypeTuple;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override String xstr() {
    if( in(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj_"+_idx;
  }
  @Override public Node ideal(GVNGCM gvn) { return in(0).is_copy(gvn,_idx); }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(in(0));
    return ((TypeTuple)c).at(_idx); // Otherwise our type is just the matching tuple slice
  }
  @Override public Type all_type() { return Type.CTRL; }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }
  
  // Used in Parser just after an if-test to sharpen the tested variables.
  // This is a mild optimization, since e.g. follow-on Loads which require a
  // non-nil check will hash to the pre-test Load, and so bypass this
  // sharpening.  
  @Override public CProjNode sharpen( GVNGCM gvn, ScopeNode scope, ScopeNode arm ) {
    Node iff = in(0);
    if( !(iff instanceof IfNode) ) return this; // Already collapsed IfNode, no sharpen
    Node test = iff.in(1);
    add_def(this);              // Self-hook to prevent accidental deletion
    Node sharp = _idx==1
      ? gvn.xform(new CastNode(this,test,Type.NSCALR))
      : gvn.con(TypeNil.NIL);
    scope.sharpen(test,sharp,arm);
    pop();                      // Remove self-hook
    return this;
  }
}
