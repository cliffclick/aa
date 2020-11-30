package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Extract a Display pointer (a TypeMemPtr) from a TypeFunPtr.
public final class FP2DispNode extends Node {
  public FP2DispNode( Node funptr ) { super(OP_FP2DISP,funptr); }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // If at a FunPtrNode, it is only making a TFP out of a code pointer and a
    // display.  Become the display (dropping the code pointer).
    Node disp = fptr2disp(in(0));
    if( disp != null ) return disp;
    // If all inputs to an Unresolved are FunPtrs with the same Display, become that display.
    if( in(0) instanceof UnresolvedNode ) {
      for( Node in : in(0)._defs ) {
        Node disp2 = fptr2disp(in);
        if( disp==null ) disp = disp2;
        else if( disp!=disp2 )
          return null;
      }
      return disp;
    }
    return null;
  }

  Node fptr2disp( Node in ) {
    if( in instanceof FunPtrNode ) {
      FunPtrNode fptr = (FunPtrNode)in;
      if( !fptr.is_forward_ref() )
        return fptr.display();
    }
    return null;
  }
  
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type t = val(0);
    return t instanceof TypeFunPtr ? ((TypeFunPtr)t)._disp.simple_ptr() : t.oob(TypeMemPtr.DISP_SIMPLE);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return def instanceof ThretNode ? TypeMem.ANYMEM : _live; }
}
