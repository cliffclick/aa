package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.*;

// Strip out the display argument from a bound function.
// Inverse of BindFP.
public class FP2DSPNode extends Node {
  final Parse _bad;
  public FP2DSPNode( Node fp, Parse bad ) { super(fp); _bad=bad; }
  @Override public String label() {return "FP2DSP"; }

  Node fp() { return in(0); }
  @Override public Type value() {
    Type fpt = fp()._val;
    if( fpt == Type.ANY || fpt == Type.ALL ) return fpt;
    if( fpt.above_center() ) return Type.ANY;
    if( fpt instanceof TypeFunPtr tfp )
      return tfp.has_dsp() ? tfp.dsp() : Type.ANY;
    // Very weak, since input is not a function ptr.
    return TypeMemPtr.ISUSED0;
  }

  private static final Type DSP_LIVE = TypeStruct.UNUSED.add_fldx(TypeFld.make("dsp",Type.ALL));
  @Override public Type live_use( int i ) { return DSP_LIVE; }

  @Override public Node ideal_reduce() {
    Node fp = fp();
    // Note: cannot bypass Fresh nodes here; might need to Fresh a display.
    if( fp instanceof BindFPNode bind )
      return bind.dsp();
    return null;
  }

  
  @Override public boolean has_tvar() { return true; }

  @Override public TV3 _set_tvar() {
    TV3 tv = fp().set_tvar();
    if( tv instanceof TVLambda fun )
      return fun.dsp();
    
    _tvar=new TVLeaf();
    new TVLambda(TVLambda.UNKNOWN_NARGS,_tvar,new TVLeaf());
    return _tvar;
  }
  
  //// Implements class HM.Lambda unification.
  //@Override public boolean unify( boolean test ) {
  //  TV3 tv = tvar(0);
  //  if( tv instanceof TVLambda fun )
  //    return tvar().unify(fun.dsp(),test); // Unify against display
  //  // Revisit if we unify to a TVLambda
  //  if( tv instanceof TVLeaf ) tv.deps_add_deep(this);
  //  // Also, we should force TVLambda here except we've no idea of nargs
  //  return false;               // No progress until lambda
  //}

  @Override public ErrMsg err( boolean fast ) {
    Type fdx = fp()._val;
    if( fdx instanceof TypeFunPtr tfp && tfp.has_dsp())
      return null;
    if( fdx instanceof TypeNil tn && tn._fidxs.test(BitsFun.EXTX) ) return null; // Call of external function
    return fast ? ErrMsg.FAST : ErrMsg.unresolved(_bad,"A function is being called, but "+fdx+" is not a function");
  }
}
