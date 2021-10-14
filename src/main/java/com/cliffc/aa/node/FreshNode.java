package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

// "fresh" the incoming TVar: make a fresh instance before unifying
public class FreshNode extends UnOrFunPtrNode {
  public FreshNode( FunNode fun, Node ld ) { super(OP_FRESH, fun, ld); }

  // The lexical scope, or null for top-level
  FunNode fun() {
    return in(0)==Env.CTL_0 ? null : (FunNode)in(0);
  }
  Node id() { return in(1); }       // The HM identifier
  TV2[] nongen() { return fun()==null ? null : fun()._nongen; }
  @Override public Node ideal_reduce() {
    if( id()==this ) return null; // Dead self-cycle
    // Remove Fresh of base type values: things that can never have structure.
    if( no_tvar_structure(_val) )
      return id();
    // Remove if TVar has already unified with the input.
    if( _tvar!=null && tvar()==id().tvar() )
     return id();

    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) { return id()._val; }
  @Override public void add_work_extra(Work work,Type old) {
    // Types changed, now might collapse
    if( !no_tvar_structure(old) && no_tvar_structure(_val) )
      Env.GVN.add_reduce(this);
  }

  @Override public TypeMem all_live() { return TypeMem.LIVE_BOT; }

  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==id() ) return _live; // Pass full liveness along
    return TypeMem.ALIVE;         // Basic aliveness for control
  }

  // Things that can never have type-variable internal structure.
  private static boolean no_tvar_structure(Type t) {
    return t.isa(TypeInt.INT64) || t.isa(TypeFlt.FLT64);
  }

  @Override public boolean unify( Work work ) {
    return id().tvar().fresh_unify(tvar(),nongen(),work);
  }
  @Override public void add_work_hm(Work work) {
    super.add_work_hm(work);
    work.add(id());
    TV2 t = id().tvar();
    if( t.nongen_in(nongen()) )
      t.add_deps_work(work); // recursive work.add(_deps)
  }

  @Override public byte op_prec() { return id().op_prec(); }
  @Override Node is_pure_call() { return id().is_pure_call(); }

  @Override public UnresolvedNode unk() { return id() instanceof UnresolvedNode ? (UnresolvedNode)id() : null; }
  @Override int nargs() { return ((UnOrFunPtrNode)id()).nargs(); }
  @Override public UnOrFunPtrNode filter(int nargs) { return ((UnOrFunPtrNode)id()).filter(nargs); }
  @Override public FunPtrNode funptr() {
    return id() instanceof UnOrFunPtrNode ? ((UnOrFunPtrNode)id()).funptr() : null;
  }

  // Two FreshNodes are only equal, if they have compatible TVars
  @Override public boolean equals(Object o) {
    if( _tvar==null ) return this==o;
    if( !(o instanceof FreshNode) ) return false;
    if( Combo.NIL_OK ) return false;
    return tvar().compatible(((FreshNode) o).tvar());
  }
}
