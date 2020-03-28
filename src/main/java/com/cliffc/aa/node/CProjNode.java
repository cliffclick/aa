package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn, int idx ) { this(OP_CPROJ,ifn,idx); }
  public CProjNode( byte op, Node ifn, int idx ) { super(op,ifn,idx); }
  @Override String xstr() {
    if( !is_dead() && in(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj_"+_idx;
  }
  @Override public Node ideal(GVNGCM gvn, int level) { return in(0).is_copy(gvn,_idx); }
  @Override public Type value(GVNGCM gvn) {
    Type c = gvn.type(in(0));  // our type is just the matching tuple slice
    if( c.isa(TypeTuple.IF_ANY) ) return Type.XCTRL;
    if( TypeTuple.IF_ALL.isa(c) ) return Type. CTRL;
    if( !(c instanceof TypeTuple) ) return Type.CTRL;
    TypeTuple ct = (TypeTuple)c;
    Type res = ct.at(_idx);
    return res==Type.XCTRL ? Type.XCTRL : Type.CTRL;
  }
  @Override public boolean basic_liveness() { return true; }
  @Override public Type all_type() { return Type.CTRL; }
  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }

}
