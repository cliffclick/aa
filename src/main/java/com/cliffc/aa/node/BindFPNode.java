package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.unimpl;

// Bind a 'this' into an unbound function pointer.  Inverse of FP2DSP.  The
// function input can also be a struct (overload) of function pointers.
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
  @Override public Type value() {
    Type tfp = fp ()==null ? TypeFunPtr.GENERIC_FUNPTR.dual() : fp()._val;
    Type dsp = dsp()==null ? Type.ANY : dsp()._val;
    return bind(tfp,dsp,_over);
  }

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
    if( def==dsp() ) return bind_live("dsp");
    Type fplive = bind_live("fp");
    return _over ? fplive.oob(TypeStruct.ISUSED) : fplive;
  }
  private Type bind_live(String name) {
    return _live instanceof TypeStruct ts ? ts.at_def(name): _live;
  }
  
  // Bind can be used by a Field, and so have a struct-liveness, and the whole of the Bind
  // is pushed into functions with
  @Override public boolean assert_live(Type live) {
    if( !(live instanceof TypeStruct ts) ) return false;
    if( _over ) return true; // Used by a Field node which will select which field is alive
    // Normal binds allow on fields "fp" and "dsp"
    for( TypeFld tf : ts )
      if( !Util.eq(tf._fld,"fp") && Util.eq(tf._fld,"dsp") )
        return false;
    return true;
  }

  @Override public Node ideal_reduce() {
    if( !_over && _live instanceof TypeStruct live ) {
      if( live.at_def("fp" )==Type.ANY ) return set_def(0,null);
      if( live.at_def("dsp")==Type.ANY ) return set_def(1,null);
    }
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() { return fp().set_tvar(); }

  @Override public boolean unify( boolean test ) {
    boolean progress = false;
    TV3 fptv = fp().tvar();
    if( _over && fptv instanceof TVStruct tvs ) {
      for( int i = 0; i < tvs.len(); i++ )
        if( !Resolvable.is_resolving(tvs.fld(i)) &&
            tvs.arg(i) instanceof TVLambda lam )
          progress |= lam.dsp().unify(dsp().tvar(), test);
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
