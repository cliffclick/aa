package com.cliffc.aa.node;

import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeTuple;

import static com.cliffc.aa.AA.*;

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
  public  FunPtrNode( String name, RetNode ret ) {
    super(OP_FUNPTR,ret);
    _name = name;
    ParmNode pdsp = ret.fun().parm(DSP_IDX);
    if( pdsp != null ) {
      pdsp.deps_add(this);
      pdsp.deps_mark();
    }
  }
  // Display (already fresh-loaded) but no name.
  public  FunPtrNode( RetNode ret ) { this(ret.fun()._name,ret); }
  public RetNode ret() { return in(0)==null ? null : (RetNode)in(0); }
  public FunNode fun() { return ret().fun(); }
  public FunNode xfun() { RetNode ret = ret(); return ret !=null && ret.in(4) instanceof FunNode ? ret.fun() : null; }
  int nargs() { return ret()._nargs; }
  int fidx() { return fun()._fidx; }
  String name() { return _name; } // Debug name, might be empty string
  // Formals from the function parms.
  // TODO: needs to come from both Combo and _t
  Type formal(int idx) { return ret().formal(idx); }

  // Self short name
  @Override public String xstr() {
    if( is_dead() || _defs._len==0 ) return "*fun";
    RetNode ret = ret();
    return ret==null ? "*fun" : "*"+_name;
  }
  // Inline longer name
  @Override String str() {
    if( is_dead() ) return "DEAD";
    if( _defs._len==0 ) return "MAKING";
    RetNode ret = ret();
    if( ret==null || ret.is_copy() ) return "gensym:"+xstr();
    FunNode fun = ret.fun();
    return fun==null ? xstr() : fun.str();
  }

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
    return TypeFunPtr.make(ret._fidx,nargs(),Type.ANY,tret.at(REZ_IDX));
  }

  @Override public boolean has_tvar() { return true; }

  @Override public TV3 _set_tvar() {
    return new TVLambda(nargs(),new TVLeaf(),ret().rez().set_tvar());
  }

  // Implements class HM.Lambda unification.
  @Override public boolean unify( boolean test ) {
    RetNode ret = ret();
    if( ret.is_copy() ) return false; // GENSYM
    FunNode fun = ret.fun();
    ParmNode[] parms = fun.parms();
    TVLambda lam = (TVLambda)tvar();

    // Each normal argument from the parms directly
    boolean progress = false;
    for( int i=DSP_IDX; i<parms.length; i++ )
      // Parms can be missing (and display might not support a TVar)
      if( parms[i]!=null ) {
        progress |= lam.arg(i).unify(parms[i].tvar(),test);
        if( test && progress ) return true;
      }
    progress |= lam.ret().unify(ret.rez().tvar(),test);

    return progress;
  }
}
