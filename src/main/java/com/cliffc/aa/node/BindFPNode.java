package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

// Bind a 'this' into an unbound function pointer.  Inverse of FP2DSP.
public class BindFPNode extends Node {
  private byte _mode; // 0 unknown, +1 adds display, -1 no-op/extra/remove
  public BindFPNode( Node fp, Node dsp ) { super(OP_BINDFP,fp,dsp); }
  @Override public String xstr() {return "BindFP"; }

  Node fp() { return in(0); }
  Node dsp() { return in(1); }

  // BindFP unifies its display and self.  
  // BindFP must be monotonic!
  // - if input has a display, flow passes display thru, and unifies straight thru.
  // - if input has  !display, flow sets display, and unifies display with the TFP display.
  //   - TFP.DISPLAY  DISPLAY
  //   -   NO_DSP      ANY    - UNKN Pass along no-dsp .
  //   -   NO_DSP      XXX    - BIND Pass along XXX dsp.  Unify TFP.DSP and DSP.
  //   -  HAS_DSP      ANY    - NOOP Pass along has-dsp.  
  //   -  HAS_DSP      XXX    - EXTR Pass along has-dsp.  
  @Override public Type value() { return bind(fp()._val, dsp()._val); }

  private Type bind(Type fun, Type dsp) {    
    if( fun instanceof TypeFunPtr tfp ) {
      // Compute the new display as the meet of old one and input
      Type mdsp = tfp.dsp().meet(dsp);
      // If the input as a display, this Bind is a no-op; flag it and this
      // cannot change.  Instead, if we are given a display and dont have one,
      // this Bind is required and cannot change.
      if( tfp.has_dsp() ) { assert _mode<=0; _mode=-1; }
      else if( TypeFunPtr.has_dsp(mdsp) ) { assert _mode>=0; _mode= 1; }
      return tfp.make_from(mdsp);
    }
    
    // Push Bind down into overloads
    if( fun instanceof TypeStruct ts ) {
      TypeFld[] tfs = TypeFlds.get(ts.len());
      for( int i=0; i<ts.len(); i++ )
        tfs[i] = ts.get(i).make_from(bind(ts.at(i),dsp));
      return ts.make_from(tfs);
    }

    // If the in(0) can never be a function nor struct, we're always a no-op.
    if( !fun.dual().isa(TypeFunPtr.GENERIC_FUNPTR) &&
        !fun.dual().isa(TypeStruct.ISUSED) )
      { assert _mode <= 0; _mode = -1; }
    
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
    // Already decided self is a no-op based on types, remove.
    if( _mode == -1 ) return fp();
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }

  @Override public boolean unify( boolean test ) {
    // Wait until types decide if this Bind is a no-op or not.
    switch( _mode ) {
    case  0: return false;      // Stall till the Types decide
    case  1: throw unimpl();
    case -1: return fp().tvar().unify(tvar(),test); // Dummy Bind, just unify straight thru

      
    default: throw unimpl();
    }
    //// No display (yet)
    //Type tfp = fp()._val, dsp = dsp()._val;
    //if( dsp == Type.ANY ) return false;
    //if( tfp == Type.ANY ) return false;
    //boolean progress = false;
    //if( tfp instanceof TypeStruct ts && fp().tvar() instanceof TVStruct tvs ) {
    //  for( int i=0; i<tvs.len(); i++ )
    //    if( !Resolvable.is_resolving(tvs.fld(i)) )
    //      progress |= _unify(ts.at(tvs.fld(i)),tvs.arg(i),test);
    //} else if( tfp instanceof TypeFunPtr && fp().tvar() instanceof TVLambda lam ) {
    //  progress |= lam.unify(tvar(),test);
    //  progress |= _unify(tfp,tvar(),test);
    //} else {
    //  // Dummy, unify the FP straight over
    //  return fp().tvar().unify(tvar(),test);
    //}
    //return progress;
  }

  private boolean _unify( Type t, TV3 tv, boolean test ) {
    if( t instanceof TypeFunPtr && tv instanceof TVLambda lam ) {
      return lam.unify(tvar(),test) |
        lam.dsp().unify(dsp().tvar(),test);
    }
    return false;
  }


  
  // Error to double-bind
  @Override public ErrMsg err( boolean fast ) {
    if( fp()._val instanceof TypeFunPtr tfp && tfp.has_dsp() &&
        dsp()._val != Type.ANY )
      throw unimpl();
    return null;
  }  
 
}
