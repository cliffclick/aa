package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.NonBlockingHashMap;
import java.util.HashSet;

// Return TVar.  Just gathers Ctrl,Mem,Val.
public class TRet extends TArgs {

  public TRet(TNode ret) { super(ret,false); assert _parms.length==3; }
  private TRet(TVar[] parms) { super(null,parms,false); }

  // Return a "fresh" copy, preserving structure
  @Override TRet _fresh( HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups) {
    TVar rez = dups.get(this);
    if( rez != null ) return (TRet)rez;
    return _fresh2(nongen,dups,new TRet(new TVar[3]));
  }

  
}
