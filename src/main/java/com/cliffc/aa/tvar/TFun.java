package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// FunPtr TVar, a classic function tvar, mapping between a TArgs and a TRet.
public class TFun extends TVar {
  TVar _args, _ret;      // Either plain TVars, or a TArg, TRet.

  public TFun(TNode fptr, TVar args, TVar ret) { super(fptr); _args = args; _ret=ret;}

  public TVar args() { TVar args = _args.find();  return args==_args ? args : (_args=args); }
  public TVar ret () { TVar ret  = _ret .find();  return ret ==_ret  ? ret  : (_ret =ret ); }

  @Override boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) {
    if( this==tv ) return true;
    if( tv.getClass()==TVar.class ) return true;
    if( !(tv instanceof TFun) ) return false;
    TFun tfun = (TFun)tv;
    if( cnt > 100 ) throw com.cliffc.aa.AA.unimpl();
    if( !args()._will_unify(tfun.args(),cnt,cyc) ) return false;
    if( !ret ()._will_unify(tfun.ret (),cnt,cyc) ) return false;
    return true;
  }

  @Override void _unify( TVar tv ) {
    assert _u!=null;            // Flagged as being unified
    TFun tfun = (TFun)tv;
    TVar arg0 = args(), arg1 = tfun.args();
    TVar ret0 = ret (), ret1 = tfun.ret ();
    arg0._unify0(arg1);
    ret0._unify0(ret1);
    _args = _ret = null;        // Clear out, now that unified
  }

  @Override boolean _eq(TVar tv) {
    assert _u==null && tv._u==null;
    if( this==tv ) return true;
    if( !(tv instanceof TFun) ) return false; // Both TFun
    TFun tfun = (TFun)tv;
    return args()._eq(tfun.args()) && ret()._eq(tfun.ret());
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("{ ");
    _args.str(sb,bs,debug).p(" -> ");
    _ret .str(sb,bs,debug).p(" }");
    return sb;
  }
}
