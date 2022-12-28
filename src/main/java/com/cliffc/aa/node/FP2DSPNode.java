package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;

import static com.cliffc.aa.AA.unimpl;

// Strip out the display argument from a bound function.
// Inverse of BindFP.
public class FP2DSPNode extends Node {
  public FP2DSPNode( Node fp ) { super(OP_FP2DSP,fp); }
  @Override public String xstr() {return "FP2DSP"; }

  Node fp() { return in(0); }
  @Override public Type value() {
    if( !(fp()._val instanceof TypeFunPtr tfp) ) return fp()._val.oob();
    assert tfp.has_dsp();
    return tfp.dsp();
  }
  
  @Override public Node ideal_reduce() {
    if( fp() instanceof BindFPNode bind ) return bind.dsp();
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }

  // Implements class HM.Lambda unification.
  @Override public boolean unify( boolean test ) {
    throw unimpl();
  }  
}
