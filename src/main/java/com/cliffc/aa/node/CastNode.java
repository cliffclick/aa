package com.cliffc.aa.node;

import com.cliffc.aa.*;

// See FunNode
public class CastNode extends Node {
  private final Type _t;                // TypeVar???
  CastNode( Node ctrl, Node ret, Type t ) { super(OP_CAST,ctrl,ret); _t=t; }
  @Override String str() { return "("+_t+")"; }
  // TODO: Can eliminate if the cast is useless
  @Override public Node ideal(GVNGCM gvn) {

    // Heuristic to inline small functions.  Look for the pattern:
    //   Cast0->Proj->Ret2->Fun
    //                Ret2->Fun
    //   Cast0->Rez->Parms->Fun
    //               Parms->Args
    // Replace with
    //   Copy_Rez->slice_args
    ProjNode proj = (ProjNode) at(0);
    RetNode ret = (RetNode) proj.at(0);
    FunNode fun = (FunNode) ret.at(2);
    Node rez = at(1);
    Node irez;
    if( rez instanceof ParmNode && rez.at(0) == fun ) { // Zero-op body
      irez = rez.at(proj._idx);  // Identity function on some param
    } else { // Else check for 1-op body
      for( Node parm : rez._defs )
        if( parm != null &&
            !(parm instanceof ParmNode && parm.at(0) == fun) &&
            !(parm instanceof ConNode) )
          return null;
      irez = rez.copy();     // Copy the entire function body
      for( Node parm : rez._defs )
        irez.add_def((parm == null || parm instanceof ConNode) ? parm : parm.at(proj._idx));
    }
    // The ProjNode becomes the FunNode input control
    proj.set_as_ctrl(gvn,fun.at(proj._idx));
    // The FunNode input path goes dead
    fun.set_def(proj._idx,gvn.con(TypeErr.ANY),gvn);
    return irez;
  }
  // TODO: Actually upcast
  @Override public Type value(GVNGCM gvn) { return gvn.type(at(1)); }
  @Override public Type all_type() { return Type.SCALAR; }
}
