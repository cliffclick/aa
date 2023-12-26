package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.TODO;

// Bind a 'this' into an unbound function pointer.  Inverse of FP2DSP.  The
// function input can also be a struct (overload) of function pointers.
public class BindFPNode extends Node {
  final boolean _over;  // Binds an Overload
  public BindFPNode( Node fp, Node dsp, boolean over ) { super(fp,dsp); _over = over; }
  @Override public String label() {return "BindFP"; }

  public Node fp () { return in(0); }
  public Node dsp() { return in(1); }

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
    if( !over && fun instanceof TypeFunPtr tfp ) {
      if( tfp.has_dsp() ) return tfp; // Already bound
      return tfp.make_from(dsp);      // Bind it
    }
    
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

  
  @Override public Type live_use( int i ) {
    // If this bind is binding an overload
    // - its being used by a resolving field, this _live is some-field live
    // - the display might be a primitive int/flt or a TMP; its all-alive
    // - the whole overload is struct-live
    // Else normal FP bind
    // - Normal value, normal uses, so struct/fp-or-dsp alive
    // - The display should be a TMP, and liveness flows
    // - The funptr should be a TFP, and liveness flows
    if( _over ) {
      return i==0 ? TypeStruct.ISUSED // Whole overload is used
        : Type.ALL;                   // Whole primitive or TMP is alive
    } else {
      return _live instanceof TypeStruct ts ? ts.at_def(i==0 ? "fp" : "dsp") : _live;
    }
  }
  
  // Bind can be used by a Field, and so have a struct-liveness, and the whole of the Bind
  // is pushed into functions with
  @Override public boolean assert_live(Type live) {
    if( !(live instanceof TypeStruct ts) ) return false;
    if( _over ) return true; // Used by a Field node which will select which field is alive
    // Normal binds allow on fields "fp" and "dsp"
    for( TypeFld tf : ts )
      if( !Util.eq(tf._fld,"fp") && !Util.eq(tf._fld,"dsp") )
        return false;
    return true;
  }

  @Override public Node ideal_reduce() {
    if( !_over && _live instanceof TypeStruct live ) {
      if( in(0)!=null && live.at_def("fp" )==Type.ANY ) return setDef(0,null);
      if( in(1)!=null && live.at_def("dsp")==Type.ANY ) return setDef(1,null);
    } else deps_add(this);      // Liveness changes, recheck
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() { return fp().set_tvar(); }

  @Override public boolean unify( boolean test ) {
    boolean progress = false;
    TV3 fptv = fp().tvar();
    if( _over && fptv instanceof TVPtr ptr ) {
      TVStruct tvs = ptr.load();
      for( int i = 0; i < tvs.len(); i++ )
        if( tvs.arg(i) instanceof TVLambda lam )
          progress |= dsp_unify(lam.dsp(), dsp(), test);
    } else if( fptv instanceof TVLambda lam ) {      
      progress |= dsp_unify(lam.dsp(), dsp(), test);
    } else {
      fptv.deps_add(this);
    }
    return progress;
  }

  private static boolean dsp_unify( TV3 dsp0, Node dsp, boolean test ) {
    // Unbound Lambda becomes bound 1st time only
    if( dsp0 == null ) {
      TV3 dsp1 = dsp.tvar();
      throw TODO();
    }
    // Already bound, do not bind again
    return false; // dsp0.unify(dsp1,test);
  }
  
  // Error to double-bind
  @Override public ErrMsg err( boolean fast ) {
    if( fp()._val instanceof TypeFunPtr tfp && tfp.has_dsp() &&
        dsp()._val != Type.ANY )
      throw TODO();
    return null;
  }  
 
}
