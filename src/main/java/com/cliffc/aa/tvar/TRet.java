package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;

// Return TVar.  Just gathers Ctrl,Mem,Val.
public class TRet extends TArgs {

  public TRet(TNode ret) { super(ret,false); assert _parms.length==3; }
  private TRet(TVar[] parms) { super(null,parms,false); }
  static public TRet fresh_new() { return new TRet(tvars(3)); }
  @Override TRet _fresh_new() { return fresh_new(); }
}
