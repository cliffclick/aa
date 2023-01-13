package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

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
      if( tfp.has_dsp() ) return tfp; // Already bound, do not overwrite
      return tfp.make_from(dsp);      // Bind
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

  @Override public Node ideal_reduce() {
    // If can never be a function nor an overload of functions, remove extra bind
    if( !_val.dual().isa(TypeFunPtr.GENERIC_FUNPTR) &&
        !_val.dual().isa(TypeStruct.ISUSED) )
      return fp();
    // Pre-bound fcn pointer, happens because double-bind on overloads
    if( fp()._val instanceof TypeFunPtr tfp && tfp.has_dsp() )
      return fp();
    
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override TV3 _set_tvar() { return fp().set_tvar(); }

  @Override public boolean unify( boolean test ) {
    TV3 tv = tvar();
    if( !(tv instanceof TVLambda lam) ) {
      if( !test ) tv.deps_add_deep(this);
      return false;
    }
    if( !(_val instanceof TypeFunPtr tfp) )
      return false;             // Wait until falls to a TFP
    if( tfp.has_dsp() ) return false;

    
    //return lam.dsp().unify(dsp().tvar(),test);
    throw unimpl();
  }
}
