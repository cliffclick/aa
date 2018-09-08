package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

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
    Type c = gvn.type_ne(in(0));
    return ((TypeTuple)c).at(_idx); // Otherwise our type is just the matching tuple slice
  }
  @Override public Type all_type() { return Type.CTRL; }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }
  
  // Used in Parser just after an if-test to sharpen the tested variables.
  // This is a mild optimization, since e.g. follow-on Loads which require a
  // non-null check will hash to the pre-test Load, and so bypass this
  // sharpening.  
  @Override public CProjNode sharpen( GVNGCM gvn, ScopeNode scope, TmpNode tmp ) {
    Node iff = in(0);
    if( !(iff instanceof IfNode) ) return this; // Already collapsed IfNode, no sharpen
    Node test = iff.in(1);
    Type pred = gvn.type(test);
    if( pred instanceof TypeErr ) return this;
    if( pred== Type.SCALAR ) return this;
    if( pred==TypeInt.BOOL ) {  // The bool test itself is either 0 or 1
      // Find and replace uses of the pred in the scope with the con
      scope.sharpen(test,gvn.con(TypeInt.con(_idx)),tmp);
      return this;
    }
    if( pred instanceof TypeNullable ) {// Check for null & oop
      assert pred.may_have_nil();         // Else the IfNode already sharpened
      Node sharp = _idx==1
        ? gvn.xform(new CastNode(this,test,((TypeNullable)pred).make_nil(TypeNullable.NOT_NIL)))
        : gvn.con(TypeOop.NIL);
      scope.sharpen(test,sharp,tmp);
      return this;
    }

    throw AA.unimpl();
  }
}
