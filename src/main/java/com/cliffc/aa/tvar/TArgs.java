package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.*;

import java.util.HashSet;

// Fun TVar, NOT FunPtr!  Gathers incoming function arguments.  Only used AFTER
// a Fun is completed, because Parms/Args are not available when a Fun first is
// created.
public class TArgs extends TVar {
  TVar[] _parms;
  public final boolean _unpacked;   // Syntactic de-sugaring on a Call, allows arg-counts to mis-match.

  private static TVar[] init(TNode fun) {
    TNode[] tns = fun.parms();
    TVar[] parms = new TVar[tns.length];
    for( int i=0; i<tns.length; i++ )
      parms[i] = tns[i]==null ? null : tns[i].tvar();
    return parms;
  }
  public TArgs(TNode fun, boolean unpacked ) { this(null,init(fun),unpacked); }
  TArgs(TNode fun, TVar[] parms, boolean unpacked) {
    super(fun);
    assert !(parms[0] instanceof TArgs);
    assert parms[0]==null || parms[0]._ns.atX(0) != _ns.atX(0) || _ns.atX(0)==null;
    _parms = parms;
    _unpacked = unpacked;
  }
  public final int nargs() { return _parms.length; }

  @Override boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) {
    if( this==tv ) return true;
    if( tv.getClass()==TVar.class ) return true;
    if( getClass()!=tv.getClass() ) return false; // Both TArgs or TRets
    TArgs targs = (TArgs)tv;
    if( _parms.length != targs._parms.length &&
        (_unpacked || targs._unpacked) ) // Both args must allow a loose-fit
      return false;
    if( cnt > 100 ) throw com.cliffc.aa.AA.unimpl(); // Infinite recursion check
    Integer ii = cyc.get(_uid);
    if( ii!=null && ii==targs._uid )
      return true;              // Assume cycle unifys; closes cyclic unification tests
    cyc.put(_uid,targs._uid);   // Start cycle
    for( int i=0; i<_parms.length; i++ ) {
      TVar tn0 =       parm(i);
      TVar tn1 = targs.parm(i);
      // null always unifies
      if( tn0!=null && tn1!=null && !tn0._will_unify(tn1,cnt+1,cyc) )
        return false;
    }
    return true;
  }

  // Get ith parm or null if OOB or null.
  // Do a find & update.
  public TVar parm(int i) {
    if( i >= _parms.length ) return null;
    TVar tv = _parms[i];
    if( tv==null ) return null;
    TVar tv2 = tv.find();
    assert !(i==0 && tv2 instanceof TArgs);
    return tv2 == tv ? tv2 : (_parms[i] = tv2);
  }

  @Override void _unify( TVar tv ) {
    assert _u!=null;            // Flagged as being unified
    TArgs targs = (TArgs)tv;
    for( int i=0; i<_parms.length; i++ ) {
      TVar tn0 =       parm(i);
      TVar tn1 = targs.parm(i);
      assert i!=0 || !(tn0 instanceof TArgs || tn1 instanceof TArgs);
      if( tn0!=null && tn1!=null ) // Dead always unfies
        tn0._unify0(tn1);
    }
    _parms = null;              // No longer need parts from 'this'
  }


  // Return a "fresh" copy, preserving structure
  @Override boolean _fresh_unify( TVar tv, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    assert _u==null;            // At top
    if( this==tv || dups.containsKey(this) )
      return false;             // Stop recursive cycles
    boolean progress = false;
    if( getClass() != tv.getClass() ){// Make a TArgs, unify to 'tv' and keep unifying.  And report progress.
      assert tv.getClass() == TVar.class;
      if( test ) return true;   // No unification during testing, but report progress
      progress = true;          // Forcing tv into a TArgs/TRet shape
      tv._u = _fresh_new();     // Fresh TArgs, with all empty parms
      tv._u._ns = tv._ns;       // Copy any nodes to the fresh
      tv._ns = null;
      tv = tv._u;               // This is the new unified 'tv'
    }
    TArgs targ = (TArgs)tv;     // Either a TArgs or a TRet
    dups.put(this,targ);        // Stop recursive cycles
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      if( parm != null )        // No parm means no additional structure
        progress |= parm._fresh_unify(targ.parm(i), nongen, dups, test);
    }
    return progress;
  }

  TArgs _fresh_new() { return new TArgs(null, tvars(_parms.length), _unpacked); }
  static TVar[] tvars(int len) {
    TVar[] tvs = new TVar[len];
    for( int i=0; i<len; i++ )
      tvs[i] = new TVar();
    return tvs;
  }

  // Flipped: does 'id' occur in 'this'
  @Override boolean _occurs_in(TVar id, VBitSet visit) {
    assert _u==null && id._u==null; // At top
    if( this==id ) return true;     // Occurs right here
    assert _uid>0;
    if( visit.tset(_uid) ) return false;
    for( TVar parm : _parms )
      if( parm!=null && parm.find()._occurs_in(id,visit) )
        return true;
    return false;
  }


  @Override boolean _eq(TVar tv) {
    assert _u==null && tv._u==null;
    if( this==tv ) return true;
    if( getClass()!=tv.getClass() ) return false; // Both TArgs or TRets
    TArgs targs = (TArgs)tv;
    if( nargs() != targs.nargs() ) return false;
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
  
  @Override void push_dep(TNode tn) {
    assert _deps==null;
    for( int i=0; i<_parms.length; i++ )
      if( parm(i) != null ) parm(i).push_dep(tn);
  }
}
