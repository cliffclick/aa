package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.Arrays;
import java.util.HashSet;

// A structured collection of TVars.  Child classes typically only unify with
// the same child class.
// - TFun has 2 parts: a TArgs and a TRet
// - TArg has at least a ctrl,mem,arg but may have many args, and all are indexed directly.
// - TRet has exactly 3 parts: ctrl,mem,rez.
// - TMem has as many parts as aliases, and can unify with other TMems where
//   the aliases do not all align: missing aliases are just new plain TVars.
// - TObj has as many parts as fields, and unifies by matching field names.
public abstract class TMulti<T extends TMulti<T>> extends TVar {
  TVar[] _parms;

  static TVar[] init(TNode fun) {
    TNode[] tns = fun.parms();
    TVar[] parms = new TVar[tns.length];
    for( int i=0; i<tns.length; i++ )
      parms[i] = tns[i]==null ? null : tns[i].tvar();
    return parms;
  }
  TMulti(TNode fun, TVar[] parms) {
    super(fun);
    _parms = parms;
  }

  // Get ith parm or null if OOB or null.
  // Do a find & update.
  public TVar parm(int i) {
    if( i >= _parms.length ) return null;
    TVar tv = _parms[i];
    if( tv==null ) return null;
    TVar tv2 = tv.find();
    return tv2 == tv ? tv2 : (_parms[i] = tv2);
  }
  public int len() { return _parms.length; }

  // Unify parts after other work is done
  @Override void _unify( TVar tv ) {
    assert _u!=null;            // Flagged as being unified
    if( tv instanceof TVDead ) return; // Dead, no parts unify
    TMulti targs = (TMulti)tv;
    if( _parms.length != targs._parms.length )
      throw com.cliffc.aa.AA.unimpl();
      //TNode.add_work_all(targs._ns);
    for( int i=0; i<_parms.length; i++ ) {
      TVar tn0 =       parm(i);
      TVar tn1 = targs.parm(i);
      if( tn0!=null ) {        // Null (shortcut for plain TVar) always unifies
        if( tn1==null ) targs.grow(i+1)[i] = tn0;
        else tn0._unify0(tn1,false);
      }
    }
    _parms = null;              // No longer need parts from 'this'
  }


  static final NonBlockingHashMapLong<Integer> CYC = new NonBlockingHashMapLong<>();
  static       boolean CYC_BUSY=false;
  @SuppressWarnings("unchecked")
  @Override boolean _will_unify(TVar tv, int cnt) {
    if( this==tv ) return true;
    if( tv.getClass()==TVar.class ) return true;
    if( getClass()!=tv.getClass() ) return false;    // Same subclasses
    if( cnt > 100 ) throw com.cliffc.aa.AA.unimpl(); // Infinite recursion check
    Integer ii = CYC.get(_uid);
    if( ii!=null && ii==tv._uid )
      return true;              // Assume cycle unifys; closes cyclic unification tests
    CYC.put(_uid,tv._uid);      // Start cycle
    T tmulti = (T)tv;
    int len = Math.min(_parms.length,tmulti._parms.length);
    for( int i=0; i<len; i++ ) {
      TVar tn0 =        parm(i);
      TVar tn1 = tmulti.parm(i);
      // null always unifies
      if( tn0!=null && tn1!=null && !tn0._will_unify(tn1,cnt+1) )
        return false;
    }
    return _will_unify0(tmulti,cnt);
  }
  // Subclass specific tests:
  // - TArg: requires same length or both are "unpacked"
  // - TMem: "extra" values are kept on both sides and will unify
  // - TObj: all field names must match
  abstract boolean _will_unify0(T tm, int cnt);


  // Return a "fresh" copy, preserving structure
  @Override boolean _fresh_unify( int cnt, TVar tv, BitsAlias news, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    assert _u==null;             // At top
    if( this==tv ) return false; // Already unified
    cnt++;  assert cnt<100;      // Infinite recursion check
    TVar prior = dups.get(this); // Get a replacement, if any
    if( prior != null ) {        // Found prior
      if( prior==tv ) return false;  // Already unified
      return test || prior.find()._unify0(tv,false); // Force structural equivalence
    }
    dups.put(this,tv);          // Stop recursive cycles, record structure mapping

    boolean progress = false;
    if( getClass() != tv.getClass() ){// Make a TMulti, unify to 'tv' and keep unifying.  And report progress.
      assert tv.getClass() == TVar.class;
      if( test ) return true;   // No unification during testing, but report progress
      progress = true;          // Forcing tv into a TMulti/TRet shape
      tv._u = _fresh_new();     // Fresh TMulti, with all empty parms
      tv._u._ns = tv._ns;       // Copy any nodes to the fresh
      tv._u.push_deps(tv._deps,null);// Copy any deps
      tv = tv._u;               // This is the new unified 'tv'
    }
    // Same subclass 'this' and 'tv'
    return _fresh_unify_recursive(cnt, progress, (TMulti)tv, news, nongen, dups, test);
  }
  // Recursive call for all parms
  boolean _fresh_unify_recursive(int cnt, boolean progress, TMulti tmulti, BitsAlias news, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    // Same subclass 'this' and 'tv'
    if( test && tmulti._parms.length < _parms.length ) return true;
    if( tmulti._parms.length < _parms.length ) {
      //TNode.add_work_all(tmulti._ns);
      //tmulti.grow(_parms.length);
      throw com.cliffc.aa.AA.unimpl();
    }
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      if( parm != null ) {      // No parm means no additional structure
        if( this instanceof TMem && news.test_recur(i) )
          continue;             // New-in-function, does not unify with pre-function
        TVar tvparm = tmulti.parm(i);
        if( tvparm==null ) {
          tmulti._parms[i] = tvparm = new TVar();
          tvparm.push_deps(tmulti._deps,null);
        }
        progress |= parm._fresh_unify(cnt,tvparm, news, nongen, dups, test);
      }
    }
    return progress;
  }

  abstract T _fresh_new();
  static TVar[] tvars(int len) {
    TVar[] tvs = new TVar[len];
    for( int i=0; i<len; i++ )
      tvs[i] = new TVar();
    return tvs;
  }

  TVar[] grow( int nlen ) {
    int len = _parms.length;
    while( nlen > len ) len<<=1;
    if( len != _parms.length ) _parms = Arrays.copyOf(_parms,len);
    return _parms;
  }

  // Flipped: does 'id' occur in 'this'
  @Override boolean _occurs_in(TVar id) {
    assert _u==null && id._u==null; // At top
    if( this==id ) return true;     // Occurs right here
    assert _uid>0;
    if( VISIT.tset(_uid) ) return false;
    for( TVar parm : _parms )
      if( parm!=null && parm.find()._occurs_in(id) )
        return true;
    return false;
  }

  // Find instances of 'tv' inside of 'this' via structural recursion.  Walk
  // the matching Type at the same time.  Report the first one found, and
  // assert all the others have the same Type.
  @Override Type _find_tvar(Type t, TVar tv, Type t2) {
    if( DUPS.tset(_uid) ) return t2; // Stop cycles
    t2 = _find_tvar_self(t,tv,t2);   // Look for direct hit
    if( tv==this ) return t2;        // Direct hit is the answer
    // Search recursively
    TypeTuple tt = (TypeTuple)t;
    for( int i=0; i<_parms.length; i++ )
      t2 = parm(i)._find_tvar(tt.at(i),tv,t2);
    return t2;
  }

  // Test all parm-based TVars for equivalence
  @Override boolean _eq(TVar tv) {
    assert _u==null && tv._u==null;
    if( this==tv ) return true;
    if( getClass()!=tv.getClass() ) return false; // Subclasses are equal
    TMulti targs = (TMulti)tv;
    if( _parms.length != targs._parms.length ) return false;
    if( DUPS.tset(_uid,targs._uid) )
      return true;              // Cyclic check works, something else will decide eq/ne
    for( int i=0; i<_parms.length; i++ ) {
      TVar tv0 =       parm(i);
      TVar tv1 = targs.parm(i);
      if( tv0 != null && tv1 != null && !tv0._eq(tv1) )
        return false;
    }
    return true;
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("[ ");
    for( TVar tn : _parms )
      if( tn==null ) sb.p("_ ");
      else tn.str(sb,bs,debug).p(' ');
    return sb.p("]");
  }

  @Override TNode push_dep(TNode tn, VBitSet visit) {
    assert _deps==null;
    if( visit==null ) visit = new VBitSet();
    if( visit.tset(_uid) ) return tn;
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      if( parm != null ) parm.push_dep(tn,visit);
    }
    return tn;
  }
  @Override Ary<TNode> push_deps(Ary<TNode> deps, VBitSet visit) {
    if( deps==null ) return null;
    assert _deps==null;
    if( visit==null ) visit = new VBitSet();
    if( visit.tset(_uid) ) return null;
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      if( parm != null ) parm.push_deps(deps,visit);
    }
    return deps;
  }
}
