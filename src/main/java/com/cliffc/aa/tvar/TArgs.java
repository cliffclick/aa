package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.*;

import java.util.HashSet;

// Fun TVar, NOT FunPtr!  Gathers incoming function arguments.  Only used AFTER
// a Fun is completed, because Parms/Args are not available when a Fun first is
// created.
public class TArgs extends TVar {
  TVar[] _parms;
  final boolean _loose;   // Syntatic de-sugaring on a Call, allows arg-counts to mis-match.

  private static TVar[] init(TNode fun) {
    TNode[] tns = fun.parms();
    TVar[] parms = new TVar[tns.length];
    for( int i=0; i<tns.length; i++ )
      parms[i] = tns[i]==null ? null : tns[i].tvar();
    return parms;
  }
  public  TArgs(TNode fun, boolean loose ) { this(fun,init(fun),loose); }
  TArgs(TNode fun, TVar[] parms, boolean loose) {
    super(fun);
    assert !(parms[0] instanceof TArgs);
    _parms = parms;
    _loose = loose;
  }
  public final int nargs() { return _parms.length; }

  @Override boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) {
    if( this==tv ) return true;
    if( tv.getClass()==TVar.class ) return true;
    if( getClass()!=tv.getClass() ) return false; // Both TArgs or TRets
    TArgs targs = (TArgs)tv;
    if( _parms.length != targs._parms.length &&
        !(_loose && targs._loose) ) // Both args allow a loose-fit
      return false;
    if( cnt > 100 ) throw com.cliffc.aa.AA.unimpl();
    Integer ii = cyc.get(_uid);
    if( ii!=null && ii==targs._uid )
      return true;              // Assume cycle unifys; closes cyclic unification tests
    cyc.put(_uid,targs._uid);   // Start cycle
    for( int i=0; i<_parms.length; i++ ) {
      // Compress out dead nodes
      TVar tn0 =       parm(i);
      TVar tn1 = targs.parm(i);
      // Dead always unifies
      if( tn0!=null && tn1!=null && !tn0._will_unify(tn1,cnt+1,cyc) )
        return false;
    }
    return true;
  }

  // Get ith parm or null if OOB or null.
  // Do a find & update.
  TVar parm(int i) {
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
  @Override TArgs _fresh( HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups) {
    TVar rez = dups.get(this);
    if( rez != null ) return (TArgs)rez;
    return _fresh2(nongen,dups,new TArgs(null,new TVar[_parms.length],_loose));
  }
  final <T extends TArgs> T _fresh2(HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, T targs) {
    dups.put(this,targs);       // Stop recursive cycles
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      targs._parms[i] = parm==null ? null : parm._fresh(nongen,dups);
    }
    return targs;
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
}
