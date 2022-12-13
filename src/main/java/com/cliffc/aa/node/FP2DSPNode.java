package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;

import static com.cliffc.aa.AA.unimpl;

// Bind a 'this' into an unbound function pointer.
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
    if( fp() instanceof FunPtrNode fptr ) return fptr.display();
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override TV3 _set_tvar() {
    // Display is included in the argument count, and is unified with first argument
    //TVLambda lam = new TVLambda(nargs()-DSP_IDX); _tvar = lam;
    //Node rez = ret().rez();
    //rez.set_tvar();
    //lam.set_ret(rez.tvar());
    throw unimpl();
  }

  // Implements class HM.Lambda unification.
  @Override public boolean unify( boolean test ) {
    throw unimpl();
  }  
}
