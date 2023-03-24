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
    super(OP_PARM,fun);
    assert idx>=0;
    _idx=idx;
    _t = t;
    _bad = bad;
  }
  @Override public boolean is_mem() { return _t==TypeMem.ALLMEM; }
  public FunNode fun() { return (FunNode) in(0); }
  @Override public String xstr() { return "Parm:"+_idx; }

  @Override public Type value() {
    // Not executing?
    Type ctl = val(0);
    if( ctl.above_center() ) return Type.ANY;
    FunNode fun = fun();

    // Last path might be Root caller (or might yet be Root caller, if Root
    // itself is still pending)
    Type t = Type.ANY;
    int len = fun.len();
    boolean wired_root = fun._defs.last() instanceof RootNode;
    if( wired_root || is_prim() || fun.unknown_callers(this) ) {
      if( wired_root ) len--;
      else Env.ROOT.deps_add(this);
      // During/after Combo, use the HM type for the GCP type instead of the given default
      if( _idx==MEM_IDX ) {
        t = Combo.pre() ? RootNode.def_mem(this) : Env.ROOT.rmem();
        Env.ROOT.deps_add(this); // Depends on Root
      } else if( _t==TypeFunPtr.THUNK ) {
        t = TypeFunPtr.THUNK.make_from(Env.ROOT.rfidxs());
      } else if( _tvar==null || is_prim() ) {
        t = _t;
      } else {
        Env.ROOT.deps_add(this); // Depends on Root
        t = tvar().as_flow(this);
        // TODO: Very expensive and rarely needed
        //_tvar.deps_add(this);
        //_tvar.deps_add_deep(this); // Updates to tvar recompute flow
      }
    }
  
    // Merge all live paths
    for( int i=1; i<len; i++ ) {
      CallNode call = (CallNode)fun.in(i);
      call.deps_add(this);
      Type tcall = call._val, t2;
      // Parm RPC grabs the RPC from the Call directly, not any Call value 
      if( _idx==0 ) t2 = TypeRPC.make(call._rpc);
      else if( !(tcall instanceof TypeTuple tt) ) t2 = tcall.oob(_t);
      else if( call._is_copy || _idx < call.nargs() ) t2 = tt.at(_idx);
      else t2 = Type.ALL;       // Error, arg out of range
      t = t.meet(t2);
    }

    return t.join(_t);
  }

  @Override public Type live_use( Node def ) { return Type.ALL; }
  
  @Override public Node ideal_reduce() {
    if( !(in(0) instanceof FunNode) )
      return in(0).is_copy(_idx); // Dying, or thunks
    FunNode fun = fun();
    if( fun._val == Type.XCTRL ) return null; // All dead, c-prop will fold up
    Node cp = fun.is_copy(0);
    if( cp!=null ) {            // FunNode is a Copy
      Node xcp = cp.in(_idx);
      if( xcp == this ) return Env.ANY; // Dead self-cycle
      return Env.GVN.add_reduce(xcp); // So return the copy
    }
    // Do not otherwise fold away, as this lets Nodes in *this* function depend
    // on values in some other function... which, if code-split, gets confused
    // (would have to re-insert the Parm).
    return null;
  }

  @Override public boolean has_tvar() { return !(_t instanceof TypeMem || _t instanceof TypeRPC); }
  
  @Override public TV3 _set_tvar() {
    TVLeaf tv = new TVLeaf();
    tv.deps_add(this);          // with Root input, value depends on tvar
    return tv;
  }

  // While Parms are mostly Phis (and yes for value flows), during unification
  // Parms are already treated by the H-M algo, and (via fresh_unify) get
  // "fresh" TVars for every input path.
  @Override public boolean unify( boolean test ) { return false; }
  
  @Override public int hashCode() { return super.hashCode()+(int)_t._hash+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode parm) ) return false;
    return _idx==parm._idx && _t==parm._t;
  }
}
