package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Combo;
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
  public FunPtrNode( String name, RetNode ret, Node env ) {
    super(ret,env);
    _name = name;
  }

  @Override String label() {
    if( _name != null ) return "*"+_name+"{}";
    FunNode fun = xfun();
    if( fun==null ) return "*{->}";
    return "*"+fun.label()+"{}";
  }
  // Already a constant
  @Override public boolean shouldCon() { return false; }

  // Display (already fresh-loaded) but no name.
  public FunPtrNode( RetNode ret, Node env ) { this(ret.fun()._name,ret,env); }
  public RetNode ret() { return in(0)==null ? null : (RetNode)in(0); }
  public Node dsp() { return in(1); }
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
    Type tret = ret._val instanceof TypeTuple tt ? tt.at(REZ_IDX) : ret._val.oob();
    // If dsp() is null, returning an UNBOUND function.
    // Else returning a *bound* function ptr, even if the display is dead,
    // and pinch to +/-SCALAR
    Type dsp;
    if( dsp() == null ) dsp = Type.ANY; // Unbound
    else {
      dsp = dsp()._val;
      dsp = dsp==Type.ANY ? TypeNil.XSCALAR
        :  (dsp==Type.ALL ? TypeNil.SCALAR : dsp);
    }
    return TypeFunPtr.make(ret._fidx,nargs(),dsp,tret);
  }

  // FunPtrs return RetNode liveness for memory
  @Override public Type live_use( int i ) {
    if( i==0 ) {
      // The RET is alive, but the FunPtr does not itself demand any memory.
      // Instead, either it escapes and Root demands memory, or it is called
      // and the Call demands memory.  Pre-Combo, however, if the FunPtr
      // exists and may-be-wired, then it acts as a proxy for some future
      // wired Call.
      return _live!=Type.ANY ? (Combo.pre() ? RootNode.removeKills(ret()) : TypeMem.ANYMEM) : Type.ANY;
    } else {
      // Display passes live along
      return _live;
    }
  }

  @Override public Node ideal_reduce() {
    // Since 2 parts liveness, could check live being not-live and remove either part
    if( dsp() != Env.XSCALAR && _live instanceof TypeStruct live && live.has("fp") && !live.has("dsp") )
      return setDef(1,Env.XSCALAR);
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
    // Set early to stop cycles on self-recursive functions
    _tvar = new TVLambda(args);
    // Display is either "ANY" meaning: no display; binding happens on load.
    // Or: bound to PartialScopeFreshNode - which is a Fresh.
    // Or: bound to a Fresh type of some struct (instanceof call)
    if( dsp()!=null && dsp()!=Env.ANY && dsp().has_tvar() ) {
      TV3 tvdsp = dsp().set_tvar();
      args[DSP_IDX].find().unify(tvdsp,false);
    }
    return _tvar;
  }

}
