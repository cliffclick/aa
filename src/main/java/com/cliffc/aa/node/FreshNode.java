package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import static com.cliffc.aa.AA.unimpl;

import java.util.Arrays;

// "fresh" the incoming TVar: make a fresh instance.
public class FreshNode extends UnOrFunPtrNode {
  TV2[] _tv2s;                  // Compacted VStack of nongen TV2s, used during "fresh"
   public FreshNode( Env.VStack vs, Node ld ) {
     super(OP_FRESH, null, ld);
     _tv2s = vs.compact();
     ld.tvar().push_dep(this);
   }

  Node id() { return in(1); }   // The HM identifier
  @Override public Node ideal_reduce() {
    if( id()==this ) return null; // Dead self-cycle
    // Remove Fresh of base type values: things that can never have structure.
    if( no_tvar_structure(_val) )
      return id();
    // Remove if TVar has already unified with the input.
    // Removes many FreshNodes but requires non-local info to put on worklist.
    // i.e. a remote unification can suddenly enable this.
    if( !tvar().unify(id().tvar(),null) ) // Unification progress?
     return id();

    // Unwind ctrl-copy
    Node cc = in(0).is_copy(0);
    if( cc!=null ) return set_def(0,cc);

    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) { return val(1); }
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
    return t.isa(TypeInt.INT64) || t.isa(TypeFlt.FLT64) || t.isa(TypeMemPtr.ISUSED0);
  }

  @Override public boolean unify( Work work ) {
    return tvar(1).fresh_unify(tvar(),_tv2s,work);
  }
  @Override public void add_work_hm(Work work) {
    work.add(in(1));
    TV2 t = tvar(1);
    if( t.nongen_in(_tv2s) )
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

  @Override public int hashCode() { return super.hashCode()+Arrays.hashCode(_tv2s); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    return (o instanceof FreshNode) && Arrays.equals(_tv2s,((FreshNode)o)._tv2s);
  }

}
