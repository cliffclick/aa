package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.*;

// Bind a 'this' into an unbound function pointer.
// Inverse of FP2DSP.
public class BindFPNode extends Node {
  public BindFPNode( Node fp, Node dsp ) { super(OP_BINDFP,fp,dsp); }
  @Override public String xstr() {return "BindFP"; }

  Node fp() { return in(0); }
  Node dsp() { return in(1); }
  @Override public Type value() { return bind(fp()._val,dsp()._val); }

  static Type bind( Type fun, Type dsp ) {
    // Push Bind down into overloads
    if( fun instanceof TypeStruct ts ) {
      TypeFld[] tfs = TypeFlds.get(ts.len());
      for( int i=0; i<ts.len(); i++ )
        tfs[i] = ts.get(i).make_from(bind(ts.at(i),dsp));
      return ts.make_from(tfs);
    }
    if( fun instanceof TypeFunPtr tfp ) {
      if( tfp==TypeFunPtr.GENERIC_FUNPTR ) return tfp; // Forward ref, do not touch
      assert tfp.dsp()==Type.ANY;
      return tfp.make_from(dsp);
    }
    return fun;
  }
  
  @Override public Type live_use(Node def) {
    // GENERIC_FUNPTR indicates the display is dead.
    if( _live==TypeFunPtr.GENERIC_FUNPTR )
      return Type.ALL.oob(def==dsp());
    return _live;
  }
  @Override boolean assert_live(Type live) { return live instanceof TypeTuple tt && tt.len()==2; }
  
  @Override public boolean has_tvar() { return true; }
  @Override TV3 _set_tvar() {
    return fp().set_tvar();
  }

  @Override public boolean unify( boolean test ) {
    TV3 tv = tvar();
    if( !(tv instanceof TVLambda lam) ) {
      if( !test ) tv.deps_add_deep(this);
      return false;
    }
    // Unify display on a bound function
    return lam.dsp().unify(dsp().tvar(),test);
  }
}
