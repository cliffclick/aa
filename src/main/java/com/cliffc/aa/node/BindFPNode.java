package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;

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

  @Override public Type live_use(Node def) {
    // GENERIC_FUNPTR indicates the display is dead.
    if( _live==TypeFunPtr.GENERIC_FUNPTR )
      return Type.ALL.oob(def==dsp());
    return _live;
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override TV3 _set_tvar() {
    return fp().set_tvar();
  }

  @Override public boolean unify( boolean test ) {
    TV3 tv = tvar();
    if( !(tv instanceof TVLambda lam) ) return false;
    // Unify display on a bound function
    return lam.dsp().unify(dsp().tvar(),test);
  }

  @Override public Node ideal_reduce() {
    if( fp() instanceof FunPtrNode fptr )
      return new FunPtrNode(fptr._name,fptr.ret(),dsp());
    
    // If the display is dead, do not bind
    if( _live==TypeFunPtr.GENERIC_FUNPTR ) return fp();
    return null;
  }
  
}
