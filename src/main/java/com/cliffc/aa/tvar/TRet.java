package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;

// Return TVar.  Just gathers Ctrl,Mem,Val.
public class TRet extends TArgs {

  public TRet(TNode ret) { super(ret,false); assert _parms.length==3; }

}
