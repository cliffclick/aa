package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// Return TVar.  Just gathers Ctrl,Mem,Val.
public class TRet extends TArgs {

  public TRet(TNode ret) { super(ret,false); assert _parms.length==3; }

  @Override boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) {
    if( this==tv ) return true;
    if( tv.getClass()==TVar.class ) return true;
    if( !(tv instanceof TRet) ) return false;
    return super._will_unify(tv,cnt,cyc);
  }

}
