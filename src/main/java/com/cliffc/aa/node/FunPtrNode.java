package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.DSP_IDX;
import static com.cliffc.aa.AA.REZ_IDX;

// See CallNode and FunNode comments. The FunPtrNode converts a RetNode into a
// TypeFunPtr with a constant fidx.  Used to allow first class functions to be
// passed about.

// FIDXs above-center are used to represent choice.  Normal FunPtrs, in both
// GCP and Opto/Iter, should be a single (low) FIDX.
//
// FunPtrNodes strictly fall during GCP; lift during Opto.
// So e.g. any -> [-15,any] -> [-15,-12] -> [+15,+12] -> [+15,all] -> all.

public final class FunPtrNode extends Node {
  public String _name;          // Optional for debug only

  // Every var use that results in a function, so actually only these FunPtrs,
  // needs to make a "fresh" copy before unification.  "Fresh" makes a
  // structural copy of the TVar, keeping TVars from Nodes currently in-scope
  // as-is, and making structural copies of out-of-scope TVars.  The only
  // interesting thing is when an out-of-scope TVar uses the same TVar
  // internally in different parts - the copy replicates this structure.  When
  // unified, it forces equivalence in the same places.
  public FunPtrNode( String name, RetNode ret ) {
    super(ret);
    _name = name;
  }

  @Override String label() {
    if( _name != null ) return "*Fun_"+_name;
    FunNode fun = xfun();
    if( fun==null ) return "*Fun";
    return "*"+fun.label();
  }
  // Already a constant
  @Override public boolean shouldCon() { return false; }
  
  // Display (already fresh-loaded) but no name.
  public  FunPtrNode( RetNode ret ) { this(ret.fun()._name,ret); }
  public RetNode ret() { return in(0)==null ? null : (RetNode)in(0); }
  public FunNode fun() { return ret().fun(); }
  public FunNode xfun() { RetNode ret = ret(); return ret !=null && ret.in(4) instanceof FunNode ? ret.fun() : null; }
  int nargs() { return ret()._nargs; }
  int fidx() { return fun()._fidx; }
  // Formals from the function parms.
  // TODO: needs to come from both Combo and _t
  Type formal(int idx) { return ret().formal(idx); }

  // Debug only: make an attempt to bind name to a function
  public void bind( String tok ) {
    _name = tok;
    fun().bind(tok);
  }

  @Override public Type value() {
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    RetNode ret = ret();
    TypeTuple tret = (TypeTuple)(ret._val instanceof TypeTuple ? ret._val : ret._val.oob(TypeTuple.RET));
    return TypeFunPtr.make_no_dsp(ret._fidx,nargs(),tret.at(REZ_IDX));
  }

  // FunPtrs return RetNode liveness for memory
  @Override public Type live_use( int i ) {
    Node ret = in(i);
    assert ret instanceof RetNode;
    // Pre-combo, Ret is alive because unwired caller may yet appear and demand
    // all memory
    FunNode fun = xfun();
    if( fun==null ) return TypeMem.ANYMEM; // Dead, no memory demand
    if( fun.unknown_callers() || fun.last() instanceof RootNode )
      return RootNode.removeKills(ret); // All mem minus KILLS
    // During/post-combo, Ret is alive only if called or escaped.
    Env.ROOT.deps_add(ret);
    if( Env.ROOT.rfidxs().test(fun._fidx) ) // Escaped
      return Env.ROOT._live;    // Whatever Root requires, we do also
    return TypeMem.ANYMEM;      // Dead, no memory demand
  }

  @Override public Node ideal_reduce() {
    // Dead display post-Combo, we can wipe out the display type
    if( _tvar!=null && tvar() instanceof TVLambda lam && !(lam.dsp() instanceof TVLeaf) &&
        _val instanceof TypeFunPtr tfp && tfp.dsp()==Type.ANY && xfun()!=null ) {
      Node dsp = xfun().parm(DSP_IDX);
      if( dsp==null ) {
        _tvar = ((TVLambda)lam.copy()).clr_dsp();
        return this;
      } else {
        dsp.deps_add(this);     // If parm deletes
      }
    }
    return null;
  }

  @Override public boolean has_tvar() { return true; }

  @Override public TV3 _set_tvar() {
    RetNode ret = ret();
    Node rez = ret.rez();
    assert rez!=null;
    Env.GVN.add_flow(this);

    FunNode fun = ret.fun();
    ParmNode[] parms = fun.parms();
    TV3[] args = new TV3[nargs()];
    args[0] = rez.set_tvar();
    for( int i=DSP_IDX; i<nargs(); i++ )
      args[i] = parms[i]==null ? new TVLeaf() : parms[i].set_tvar();
    return new TVLambda(args);
  }
  
}
