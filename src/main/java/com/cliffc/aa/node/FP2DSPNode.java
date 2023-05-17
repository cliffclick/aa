package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.tvar.TVLeaf;

// Strip out the display argument from a bound function.
// Inverse of BindFP.
public class FP2DSPNode extends Node {
  final Parse _bad;
  public FP2DSPNode( Node fp, Parse bad ) { super(OP_FP2DSP,fp); _bad=bad; }
  @Override public String xstr() {return "FP2DSP"; }

  Node fp() { return in(0); }
  @Override public Type value() {
    Type fpt = fp()._val;
    if( fpt == Type.ANY || fpt == Type.ALL ) return fpt;
    return (fpt instanceof TypeFunPtr tfp) ? tfp.dsp() : fpt.oob();
  }

  @Override public Node ideal_reduce() {
    Node fp = fp();
    // Note: cannoy bypass Fresh nodes here; might need to Fresh a display.
    if( fp instanceof BindFPNode bind )
      return bind.dsp();
    fp.deps_add(this);
    if( fp!=fp() ) fp().deps_add(this);
    return null;
  }

  
  @Override public boolean has_tvar() { return true; }

  // Implements class HM.Lambda unification.
  @Override public boolean unify( boolean test ) {
    TV3 tv = tvar(0);
    if( tv instanceof TVLambda fun )
      return tvar().unify(fun.dsp(),test); // Unify against display
    // Revisit if we unify to a TVLambda
    if( tv instanceof TVLeaf ) tv.deps_add_deep(this);
    // Also, we should force TVLambda here except we've no idea of nargs
    return false;               // No progress until lambda
  }

  @Override public ErrMsg err( boolean fast ) {
    Type fdx = fp()._val;
    if( fdx instanceof TypeFunPtr tfp && tfp.has_dsp())
      return null;
    if( fdx instanceof TypeNil tn && tn._fidxs.test(BitsFun.EXTX) ) return null; // Call of external function
    return fast ? ErrMsg.FAST : ErrMsg.unresolved(_bad,"A function is being called, but "+fdx+" is not a function");
  }
}
