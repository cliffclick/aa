package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.TODO;

// Bind a 'this' into an unbound function pointer.  Inverse of FP2DSP.  The
// function input can also be a struct (overload) of function pointers.

// --- PLAN A -----------------------------------------------------------------
// "1+2" -   Normal Bind on oper
//   Parser emits:
//   Load from "1".CLZ of "_+_".  Gets an overload, no binding.
//   DynLoad "_" from overload, gets a fcn  Does an actual mem Load.
//   Bind fcn with DISPLAY "1", GOOD.  Normal Bind.

// "x.y" -   Normal Bind on normal load "free Bind on every Load!"  Makes method-calls on structs work out.
//   Parser emits:
//   Load from "x" of "y".
//   Because: Parser cannot know, so must insert Bind
//   THIS IS METHOD-CALLS ON STRUCTS: "x.toString()"
//   Bind loaded "y" with "x", in case "y" is a fcn; MAYBE.
//   As soon as "y" canNOT be a unbound function, Bind is a no-op, removes.
//   If "y" becomes e.g. a TMP, this is NOT a fcn, still remove.

// "1._+_" - Oper Bind from Oper Load
//   Parser emits:
//   Load from "1".CLZ of "_+_".  Gets an overload.
//   Bind loaded "_+_" with "1".  Bind is marked as GOOD
//   As soon as "_+_" turns into a TMP, binds deep, produces a Deep Ptr
//   PRODUCES A SPECIAL DEEP-PTR TYPE, NEVER SEEN ELSEWHERE
//   Error to meet DEEP & not-DEEP ptrs!  Falls to e.g SCALAR.

// Loads against Deep Ptrs are field selects; ignore memory

// "._"
//   Parser emits:
//   DynLoad, selects 1 bound fcn from many.  Deep Ptr: does field select.
//   Because: Parser cannot know, so must insert Bind as MAYBE.
//   Value is a bound fcn, Bind is a no-op removes.

// Summary:
//   Binds are normal or oper, and can be no-op.
//   Both   Binds of Deep Ptrs are no-ops, removed.
//   Normal Binds bind FPtrs, or if cannot be a FPtr (join too high), become no-op, removes
//   Oper   Binds produce a Deep Ptr from a TMP; of other things go to ALL (error)
//   Loads (both kinds) of Deep Ptrs do field selects, ignore memory



public class BindFPNode extends Node {
  // 3 choices=
  // - +1 - always a good Bind
  // -  0 - maybe; good if gets an unbounds DSP on flow during Combo; cant tell during Combo.pre
  // - -1 - BAD; double-bind during Combo, or local double-bind.
  byte _good;  // 
  
  public BindFPNode( Node fp, Node dsp ) { this(fp,dsp,1); }
  public BindFPNode( Node fp, Node dsp, int good ) { super(fp,dsp); _good = (byte)good; }
  @Override public String label() {return "BindFP"; }

  public Node fp () { return in(0); }
  public Node dsp() { return in(1); }

  void setBad () { if( _good==0 ) _good=-1; else assert _good==-1; }
  boolean isGood () { return _good== 1; }
  boolean isBad  () { return _good==-1; }
  boolean isMaybe() { return _good== 0; }

  
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
    Type fun = fp ()._val;
    if( localDoubleBind() ) setBad();
    // Known bad, awaiting deletion
    if( isBad() )
      return fun;
    
    // Push Bind down into overloads
    if( fun instanceof TypeMemPtr tmp ) {
      if( tmp.is_prim() ) { setBad(); return fun; }
      // Expect fun to be simple
      assert tmp.is_simple_ptr();
      // Get the sharper memory struct
      TypeMem mem = (TypeMem)in(0).in(AA.MEM_IDX)._val;
      TypeStruct ts = mem.ld(tmp);
      // Bind all the functions
      TypeFld[] tfs = TypeFlds.get(ts.len());
      for( int i=0; i<ts.len(); i++ ) {
        TypeFld fld = ts.get(i);
        tfs[i] = Util.eq(fld._fld,TypeFld.CLZ) ? fld : fld.make_from(bind(fld._t));
      }
      return tmp.make_from(ts.make_from(tfs));
    } else
      return bind(fun);
  }

  Type bind(Type fun) {
    Type dsp = dsp()._val;
    assert !(fun instanceof TypeMemPtr);
    if( !(fun instanceof TypeFunPtr tfp) ) {
      if( !canBeFun(fun) ) setBad();
      return fun;
    }
    
    if( !Combo.pre() ) {
      // Double-bind is bad during and after Combo
      if( tfp.has_dsp() ) { setBad(); return fun; }
    }
    // Pre-combo, GOOD binds force DSP, MAYBEs meet
    return tfp.make_from(isGood() ? dsp : tfp.dsp().meet(dsp));
  }
  
  // Bind-after-Bind is always bad
  private boolean localDoubleBind() {
    return dsp() instanceof BindFPNode;
  }

  
  // Displays are always alive, if the Bind is alive.  However, if the Bind is
  // binding an overload the result is a struct-liveness instead just ALL.
  @Override public Type live_use( int i ) {
    // - The display should be a TMP, and liveness flows
    // - The funptr  should be a TFP, and liveness flows
    return _live instanceof TypeStruct ts ? ts.at_def(i==0 ? "fp" : "dsp") : _live;
  }
  
  @Override public boolean assert_live(Type live) {
    if( !(live instanceof TypeStruct ts) ) return false;
    // Normal binds allow on fields "fp" and "dsp"
    for( TypeFld tf : ts )
      if( !Util.eq(tf._fld,"fp") && !Util.eq(tf._fld,"dsp") )
        return false;
    return true;
  }

  // If LIFTING and fpv is low , can lift to a function.
  // If FALLING and fpv is high, can fall to a function.
  private static boolean canBeFun(Type fpv) {
    return Combo.during()
      ? fpv.isa(TypeFunPtr.GENERIC_FUNPTR)
      : TypeFunPtr.GENERIC_FUNPTR.dual().isa(fpv);
  }
  
  @Override public Node ideal_reduce() {
    // Locally broken
    if( localDoubleBind() )
      setBad();
    
    // Check that this is a "maybe Bind"
    if( isMaybe() ) {
      Type fpv = fp()._val;
      if( fpv.above_center() || // float is dead, no need to bind
          // Already bound, no double bind
         (fpv instanceof TypeFunPtr tfp && tfp.has_dsp()) ||
          // Sideways, BIND is extra, remove
          !canBeFun(fpv) )
        // Remove unneeded Bind
        setBad();
    }

    if( isBad() )
      return fp();

    // One or the other input is dead
    if( _live instanceof TypeStruct live ) {
      if( live.at_def("fp" )==Type.ANY )
        throw TODO(); // return dsp(); // return setDef(0,null);
      if( live.at_def("dsp")==Type.ANY )
        // Assume no users need the dsp, since its dead.
        return fp();
    } else deps_add(this);      // Liveness changes, recheck
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    dsp().set_tvar();
    return fp().set_tvar();
  }

  @Override public boolean unify( boolean test ) {
    assert dsp()!=null;         // Removed if null
    TV3 fptv = fp ().tvar();
    TV3 dsp  = dsp().tvar();
    if( fptv instanceof TVLambda lam )
      return dsp.unify(lam.dsp(),test);
    // Deep bind
    if( fptv instanceof TVPtr ptr ) {
      boolean progress = false;
      TVStruct ts = ptr.load();
      for( int i=0; i<ts.len(); i++ ) {
        TV3 arg = ts.arg(i);
        if( arg instanceof TVLambda lam )
          progress |= dsp.find().unify(lam.dsp(),test);
      }
      return progress;
    }
    // we can get here for junk Binds, where the "_oper" field is set to a
    // non-oper, and we will not know the Bind is junk until mid-combo.
    fptv.deps_add(this);
    return false;
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
