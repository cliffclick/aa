package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// Fun TVar, NOT FunPtr!  Gathers incoming function arguments.  Only used AFTER
// a Fun is completed, because Parms/Args are not available when a Fun first is
// created.
public class TArgs extends TVar {
  TVar[] _parms;
  final boolean _loose;   // Syntatic de-sugaring on a Call, allows arg-counts to mis-match.

  public TArgs(TNode fun, boolean loose ) {
    super(fun);
    TNode[] parms = fun.parms();
    _parms = new TVar[parms.length];
    for( int i=0; i<parms.length; i++ )
      _parms[i] = parms[i]==null ? null : parms[i].tvar();
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
    return tv2 == tv ? tv2 : (_parms[i] = tv2);
  }

  @Override void _unify( TVar tv ) {
    assert _u!=null;            // Flagged as being unified
    TArgs targs = (TArgs)tv;
    for( int i=0; i<_parms.length; i++ ) {
      TVar tn0 =       parm(i);
      TVar tn1 = targs.parm(i);
      if( tn0!=null && tn1!=null ) // Dead always unfies
        tn0._unify0(tn1);
    }
    _parms = null;              // No longer need parts from 'this'
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
