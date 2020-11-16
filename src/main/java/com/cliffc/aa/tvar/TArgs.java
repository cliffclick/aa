package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// Fun TVar, NOT FunPtr!  Gathers incoming function arguments.  Only used AFTER
// a Fun is completed, because Parms/Args are not available when a Fun first is
// created.
public class TArgs extends TVar {
  final TNode[] _parms;
  final boolean _loose;   // Syntatic de-sugaring on a Call, allows arg-counts to mis-match.

  public TArgs(TNode fun, boolean loose ) { super(fun); _parms = fun.parms(); _loose = loose; }

  @Override boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) {
    if( this==tv ) return true;
    if( tv.getClass()==TVar.class ) return true;
    if( !(tv instanceof TArgs) ) return false;
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
      TNode tn0 =                               _parms[i];
      TNode tn1 = i<targs._parms.length ? targs._parms[i] : null;
      if( tn0 != null && tn0.is_dead() )       _parms[i] = tn0 = null;
      if( tn1 != null && tn1.is_dead() ) targs._parms[i] = tn1 = null;
      // Dead always unifies
      if( tn0!=null && tn1!=null && !tn0.tvar()._will_unify(tn1.tvar(),cnt+1,cyc) )
        return false;
    }
    return true;
  }

  @Override void _unify( TVar tv ) {
    if( tv.getClass()==TVar.class ) return;
    TArgs targs = (TArgs)tv;
    for( int i=0; i<_parms.length; i++ ) {
      TNode tn0 =                               _parms[i];
      TNode tn1 = i<targs._parms.length ? targs._parms[i] : null;
      if( tn0!=null && tn1!=null ) // Dead always unfies
        tn0.tvar()._unify0(tn1.tvar());
    }
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("[ ");
    for( TNode tn : _parms )
      if( tn==null ) sb.p("_ ");
      else tn.tvar().str(sb,bs,debug).p(' ');
    return sb.p("]");
  }
}
