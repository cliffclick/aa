package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import java.util.HashSet;

import static com.cliffc.aa.AA.MEM_IDX;

// FunPtr TVar, a classic function tvar, mapping between a TArgs and a TRet.
public class TFun extends TMulti<TFun> {
  public HashSet<TVar> _nongen; // "Non-generative" set of TVars; TVars from all variables visible in the defining scope

  public TFun(TNode fptr, HashSet<TVar> nongen, TVar args, TVar ret) { super(fptr,new TVar[]{args,ret}); _nongen = nongen; }
  private TFun() { this(null,null,new TVar(),new TVar()); }
  @Override public TVar reset_tnode(TNode tn) {
    int idx = _ns.find(tn);
    if( idx!=-1 ) _ns.remove(idx);
    return new TFun(tn,_nongen,new TVar(),new TVar());
  }

  public TVar args() { return parm(0); }
  public TVar ret () { return parm(1); }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TFun tfun, int cnt) { assert _parms.length==2 && tfun._parms.length==2; return true; }
  @Override TFun _fresh_new() { return new TFun(); }

  // Unify 'this' into 'that', except make a 'fresh' clone of 'this' before
  // unification, so 'this' is unchanged.  Instead 'that' picks up any
  // structure from 'this'.  Returns true for progress.
  public boolean fresh_unify(TVar args, TVar ret, boolean test, TNode dep) {
    assert _u==null;            // Already top
    assert !CYC_BUSY && CYC.isEmpty();
    CYC_BUSY=true;
    boolean will_unify =
      args()._will_unify(args,0) &&
      ret ()._will_unify(ret ,0);
    CYC.clear();
    CYC_BUSY=false;
    if( !will_unify ) return false; // No change
    if( !test ) {                   // No change if testing
      args.push_dep(dep,null);
      ret .push_dep(dep,null);
    }
    TArgs argz; TRet retz;
    BitsAlias news = BitsAlias.EMPTY; // New-in-function set; will not unify with pre-function memory
    if( args() instanceof TArgs && (argz=(TArgs)args()).parm(MEM_IDX) instanceof TMem &&
        ret () instanceof TRet  && (retz=(TRet )ret ()).parm(MEM_IDX) instanceof TMem ) {
      TMem argmem = (TMem)argz.parm(MEM_IDX);
      TMem retmem = (TMem)retz.parm(MEM_IDX);
      for( int i=0; i<retmem._parms.length; i++ )
        if( retmem._parms[i]!=null && (i>=argmem._parms.length || argmem._parms[i]==null) )
          news = news.set(i);
    }
    NonBlockingHashMap<TVar,TVar> dups = new NonBlockingHashMap<>();
    return                                          // If testing, still must call both to check for progress
      args()._fresh_unify(0,args,news,_nongen,dups,test) | // NO SHORT-CIRCUIT: NOTE: '|' NOT '||'
      ret ()._fresh_unify(0,ret ,news,_nongen,dups,test);  // Must do both halves always
  }

  // Find instances of 'tv' inside of 'this' via structural recursion.  Walk
  // the matching Type at the same time.  Report the first one found, and
  // assert all the others have the same Type.
  @Override Type _find_tvar(Type t, TVar tv, Type t2) {
    if( DUPS.tset(_uid) ) return t2; // Stop cycles
    t2 = _find_tvar_self(t,tv,t2);   // Look for direct hit
    if( tv==this ) return t2;        // Direct hit is the answer
    // Search recursively
    assert t==Type.ALL || t==Type.ANY || t instanceof TypeFunPtr;
    // TODO: There are no *local* Types in a TypeFunPtr.  We can get the FIDXS
    // & thence the FunNodes & TypeFunSigs, but these are not local.  I assume
    // I am not interested in such remote types (no type benefit accrues here)
    // but not really sure, hence the TODO.
    return t2;
  }
  
  
  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("{ ");
    _parms[0].str(sb,bs,debug).p(" -> ");
    _parms[1].str(sb,bs,debug).p(" }");
    return sb;
  }
}
