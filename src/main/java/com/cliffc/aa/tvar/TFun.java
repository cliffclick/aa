package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// FunPtr TVar, a classic function tvar, mapping between a TArgs and a TRet.
public class TFun extends TVar {
  TVar _args, _ret;               // Either plain TVars, or a TArg, TRet.

  public TFun(TNode fptr, TVar args, TVar ret) { super(fptr); _args = args; _ret=ret;}

  @Override boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) {
    if( this==tv ) return true;
    if( tv.getClass()==TVar.class ) return true;
    if( !(tv instanceof TFun) ) return false;
    TFun tfun = (TFun)tv;
    if( cnt > 100 ) throw com.cliffc.aa.AA.unimpl();
    if( !_args._will_unify(tfun._args,cnt,cyc) ) return false;
    if( !_ret ._will_unify(tfun._ret ,cnt,cyc) ) return false;
    return true;
  }

  @Override void _unify( TVar tv ) {
    if( tv.getClass()==TVar.class ) return;
    TFun tfun = (TFun)tv;
    _args.find()._unify0(tfun._args.find());
    _ret .find()._unify0(tfun._ret .find());
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("{ ");
    _args.str(sb,bs,debug).p(" -> ");
    _ret .str(sb,bs,debug).p(" }");
    return sb;
  }
}
