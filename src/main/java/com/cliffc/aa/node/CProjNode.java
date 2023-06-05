package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import static com.cliffc.aa.AA.MEM_IDX;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn ) { this(ifn,AA.CTL_IDX); }
  public CProjNode( Node ifn, int idx ) { super(OP_CPROJ,ifn,idx); }
  @Override public String xstr() {
    if( !is_dead() && in(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj"+_idx;
  }
  @Override boolean is_CFG() { return in(0).is_CFG(); }
  @Override public Type value() {
    if( in(0)._op==OP_ROOT ) return Type.CTRL; // Program Start
    // Normal projection, except pinch to CTRL.
    Type x = super.value();
    if( x==Type.ANY ) return Type.XCTRL;
    if( x==Type.ALL ) return Type. CTRL;
    return x;
  }
  @Override Type live_use( int i ) { return i==MEM_IDX ? TypeMem.ANYMEM : Type.ALL; }

  // Strictly reducing
  @Override public Node ideal_reduce() {
    Node c = in(0).is_copy(_idx);
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
