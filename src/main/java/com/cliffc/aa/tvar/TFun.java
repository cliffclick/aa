package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.*;
import java.util.HashSet;

// FunPtr TVar, a classic function tvar, mapping between a TArgs and a TRet.
public class TFun extends TMulti<TFun> {
  public HashSet<TVar> _nongen; // "Non-generative" set of TVars; TVars from all variables visible in the defining scope

  public TFun(TNode fptr, HashSet<TVar> nongen, TVar args, TVar ret) { super(fptr,new TVar[]{args,ret}); _nongen = nongen; }
  private TFun() { this(null,null,new TVar(),new TVar()); }

  public TVar args() { return parm(0); }
  public TVar ret () { return parm(1); }

  @Override void _unify( TVar tv ) {
    assert _u!=null;            // Flagged as being unified
    TFun tfun = (TFun)tv;
    TVar arg0 = args(), arg1 = tfun.args();
    TVar ret0 = ret (), ret1 = tfun.ret ();
    arg0._unify0(arg1);
    ret0._unify0(ret1);
  }
  
  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TFun tfun) { assert _parms.length==2 && tfun._parms.length==2; return true; }

  @Override TArgs _fresh_new() {
    throw com.cliffc.aa.AA.unimpl();
  }

  // Unify 'this' into 'that', except make a 'fresh' clone of 'this' before
  // unification, so 'this' is unchanged.  Instead 'that' picks up any
  // structure from 'this'.  Returns true for progress.
  public boolean fresh_unify(TVar args, TVar ret, boolean test, TNode dep) {
    assert _u==null;            // Already top
    args().push_dep(dep);
    ret ().push_dep(dep);
    assert !CYC_BUSY && CYC.isEmpty();
    CYC_BUSY=true;
    boolean will_unify =
      args()._will_unify(args,0) &&
      ret ()._will_unify(ret ,0);
    CYC.clear();
    CYC_BUSY=false;
    if( !will_unify ) return false; // No change
    
    NonBlockingHashMap<TVar,TVar> dups = new NonBlockingHashMap<>();
    return
      args()._fresh_unify(args,_nongen,dups,test) | // NO SHORT-CIRCUIT: NOTE: '|' NOT '||'
      ret ()._fresh_unify(ret ,_nongen,dups,test);  // Must do both halves always
  }
  
  @Override boolean _fresh_unify(TVar tv, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    assert _u==null;            // At top
    if( this==tv || dups.containsKey(this) )
      return false;             // Stop recursive cycles
    boolean progress = false;
    if( !(tv instanceof TFun) ) {   // Make a TFun, unify to 'tv' and keep unifying.  And report progress.
      if( test ) return true;       // No unification during testing, but report progress
      assert tv.getClass() == TVar.class;
      progress = true;          // Forcing tv into a TArgs/TRet shape
      tv._u = new TFun();       // Fresh TArgs, with all empty parms
      tv._u._ns = tv._ns;       // Copy any nodes to the fresh
      tv._ns = null;
      tv = tv._u;               // This is the new unified 'tv'
    }
    TFun tfun = (TFun)tv;
    dups.put(this,tfun);        // Stop recursive cycles
    progress |= args()._fresh_unify(tfun.args(),_nongen,dups,test);
    progress |= ret ()._fresh_unify(tfun.ret (),_nongen,dups,test);
    return progress;
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("{ ");
    _parms[0].str(sb,bs,debug).p(" -> ");
    _parms[1].str(sb,bs,debug).p(" }");
    return sb;
  }
}
