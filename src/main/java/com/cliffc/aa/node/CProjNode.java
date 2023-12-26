package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import static com.cliffc.aa.AA.MEM_IDX;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn ) { this(ifn,AA.CTL_IDX); }
  public CProjNode( Node ifn, int idx ) { super(ifn,idx); }
  @Override public String label() {
    if( !isDead() && in(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj"+_idx;
  }
  @Override public boolean isCFG() { return in(0).isCFG(); }
  @Override public Type value() {
    if( in(0) instanceof RootNode ) return Type.CTRL; // Program Start
    // Normal projection, except pinch to CTRL.
    return super.value().oob(Type.CTRL);
  }
  @Override Type live_use( int i ) { return i==MEM_IDX ? TypeMem.ANYMEM : Type.ALL; }

  // Strictly reducing
  @Override public Node ideal_reduce() {
    Node c = in(0).isCopy(_idx);
    if( c != null ) {
      if( c==this ) return null; // Dead self-loop
      // Folding IF control flow against a half CopyCal, might need to fold again
      if( c._live instanceof TypeMem )
        return null;            // Stall till parent folds
      return c; 
    }
    return null;
  }

  @Override public boolean has_tvar() { return false; }

}
