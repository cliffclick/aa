package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.DSP_IDX;
import static com.cliffc.aa.AA.unimpl;

// Bind a 'this' into an unbound function pointer.  Inverse of FP2DSP.
public class BindFPNode extends Node {
  final boolean _over;  // Binds an Overload
  public BindFPNode( Node fp, Node dsp, boolean over ) { super(OP_BINDFP,fp,dsp); _over = over; }
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
  @Override public Type value() { return bind(fp()._val, dsp()._val,_over); }

  private Type bind(Type fun, Type dsp, boolean over) {    
    if( !over && fun instanceof TypeFunPtr tfp )
        return tfp.make_from(dsp);
    
    // Push Bind down into overloads
    if( over && fun instanceof TypeStruct ts ) {
      TypeFld[] tfs = TypeFlds.get(ts.len());
      for( int i=0; i<ts.len(); i++ )
        tfs[i] = ts.get(i).make_from(bind(ts.at(i),dsp,false));
      return ts.make_from(tfs);
    }
    
    return fun;
  }

  // Displays are always alive, if the Bind is alive.  However, if the Bind is
  // binding an overload the result is a struct-liveness instead just ALL.
  @Override public Type live_use(Node def) {
    if( def==dsp() ) return Type.ALL;
    return _over ? TypeStruct.ISUSED : Type.ALL;
  }
  // Bind can be used by a Field, and so have a struct-liveness
  @Override public boolean assert_live(Type live) { return live instanceof TypeStruct; }

  @Override public Node ideal_reduce() {
    // Check for early bind of an anonymous function which is not using the display.
    if( fp()._val instanceof TypeFunPtr tptr ) {
      int fidx = tptr.fidxs().abit();
      if( fidx>0 ) {
        RetNode ret = RetNode.get(fidx);
        if( ret!=null && !ret.is_copy() ) {
          Node dsp = ret.fun().parm(DSP_IDX);
          if( dsp==null ) return fp(); // Display is dead, no need to bind
          else dsp.deps_add(this);     // 
        }
      }
    }

    return null;
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() { return fp().set_tvar(); }

  @Override public boolean unify( boolean test ) {
    boolean progress = false;
    TV3 fptv = fp().tvar();
    if( _over ) {
    //if( _over && fptv instanceof TVClz fpz ) {
    //  TVStruct tvs = fpz.rhs();
    //  for( int i = 0; i < tvs.len(); i++ )
    //    if( !Resolvable.is_resolving(tvs.fld(i)) &&
    //        tvs.arg(i) instanceof TVLambda lam )
    //      progress |= lam.dsp().unify(dsp().tvar(), test);
      throw unimpl();
    } else if( fptv instanceof TVLambda lam ) {
      progress |= lam.dsp().unify(dsp().tvar(),test);
    }
    return progress;
  }
  private boolean _unify(Type t, TV3 tv, boolean test ) {
    if( t instanceof TypeFunPtr && tv instanceof TVLambda lam ) {
      return lam.dsp().unify(dsp().tvar(),test);
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
