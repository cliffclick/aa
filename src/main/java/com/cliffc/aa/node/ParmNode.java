package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.MEM_IDX;


// Function parameter node; almost just a Phi with an order.  There is a dense
// numbering matching function arguments, e.g. MEM_IDX for memory.
public class ParmNode extends Node {
  public final int _idx; // Parameter index, MEM_IDX, DSP_IDX is display, ARG_IDX+ normal args
  public final Type _t;
  public final Parse _bad;

  public ParmNode( int idx, FunNode fun, Parse bad, Type t ) {
    super(fun);
    assert idx>=0;
    _idx=idx;
    _t = t;
    _bad = bad;
  }
  @Override public String label() { return "Parm:"+_idx; }
  @Override public boolean isMem() { return _t instanceof TypeMem; }
  @Override public boolean isMultiTail() { return true; }
  public FunNode fun() { return (FunNode) in(0); }

  @Override public Type value() {
    if( isPrim() ) return _t;   // Prims, executed or not, always conservative
    // Not executing?
    Type ctl = val(0);
    if( ctl.above_center() ) return Type.ANY;
    FunNode fun = fun();

    // Last path might be Root caller (or might yet be Root caller, if Root
    // itself is still pending)
    Type t = Type.ANY;
    int len = fun.len();
    boolean wired_root = fun.last() instanceof RootNode;
    if( wired_root || fun.unknown_callers() ) {
      if( wired_root ) len--;
      // During/after Combo, use the HM type for the GCP type instead of the given default
      if( _idx==MEM_IDX ) {
        t = Combo.pre() ? RootNode.defMem(this) : Env.ROOT.rmem(this);
      } else if( Combo.pre() ) {
        t = _t==TypeNil.SCALAR ? Env.ROOT.ext_scalar(this) : _t;
      } else if( has_tvar() ) {
        t = tvar().as_flow(this);
      } else {
        t = _t;
      }
    }

    // Merge all live paths
    for( int i=1; i<len; i++ ) {
      if( fun.in(i) instanceof CallNode call ) {
        call.deps_add_live(this);
        Type tcall = call._val, t2;
        // Parm RPC grabs the RPC from the Call directly, not any Call value
        if( _idx==0 ) t2 = TypeRPC.make(call._rpc);
        else if( !(tcall instanceof TypeTuple tt) ) t2 = tcall;
        else if( call._is_copy || _idx < call.nargs() ) t2 = tt.at(_idx);
        else t2 = Type.ALL;       // Error, arg out of range
        t = t.meet(t2);
      } else
        return _t;
    }

    return t.join(_t);
  }

  @Override public Type live_use( int i ) { return Type.ALL; }

  @Override public Node ideal_reduce() {
    if( !(in(0) instanceof FunNode) )
      return in(0).isCopy(_idx); // Dying, or thunks
    FunNode fun = fun();
    if( fun._val == Type.XCTRL ) return null; // All dead, c-prop will fold up
    Node cp = fun.isCopy(0);
    if( cp!=null ) {            // FunNode is a Copy
      if( _idx==0 ) return null; // RPC vs a CopyCall, is dead, no semantics
      Node xcp = cp.in(_idx);
      if( xcp == this ) return Env.ANY; // Dead self-cycle
      return Env.GVN.add_reduce(xcp); // So return the copy
    }
    // Do not otherwise fold away, as this lets Nodes in *this* function depend
    // on values in some other function... which, if code-split, gets confused
    // (would have to re-insert the Parm).
    return null;
  }

  @Override public boolean has_tvar() { return !(_t instanceof TypeRPC) && !isMem(); }

  @Override public TV3 _set_tvar() {
    if( isPrim() && _t==TypeInt.INT64 ) return PrimNode.PINT.tvar();
    if( isPrim() && _t==TypeFlt.FLT64 ) return PrimNode.PFLT.tvar();
    TV3 tv = new TVLeaf();
    tv.deps_add(this);          // with Root input, value depends on tvar
    return tv;
  }

  // While Parms are mostly Phis (and yes for value flows), during unification
  // Parms are already treated by the H-M algo, and (via fresh_unify) get
  // "fresh" TVars for every input path.
  @Override public boolean unify( boolean test ) { return false; }

  @Override int hash() { return (int)_t._hash+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode parm) ) return false;
    return _idx==parm._idx && _t==parm._t;
  }
}
