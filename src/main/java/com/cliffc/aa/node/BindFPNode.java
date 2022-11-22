package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;

import static com.cliffc.aa.AA.DSP_IDX;
import static com.cliffc.aa.AA.unimpl;

// Bind a 'this' into an unbound function pointer.
public class BindFPNode extends Node {
  public BindFPNode( Node fp, Node dsp ) { super(OP_BINDFP,fp,dsp); }
  @Override public String xstr() {return "BindFP"; }

  Node fp() { return in(0); }
  Node dsp() { return in(1); }
  @Override public Type value() {
    if( !(fp()._val instanceof TypeFunPtr tfp) ) return fp()._val.oob();
    assert !tfp.has_dsp();
    return tfp.make_from(dsp()._val);
  }
  @Override public boolean has_tvar() { return true; }
  @Override public void set_tvar() {
    if( _tvar!=null ) return;
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
