package com.cliffc.aa.tvar;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

/** A type error.  A collection of un-unifiable TV3s
 *
 */
public class TVErr extends TV3 {

  static final int XSTR=0;
  static final int XFUN=1;
  static final int XMAX=2;

  TVErr() { super(false,new TV3[XMAX]); }

  @Override public TVStruct as_struct() { return (TVStruct)arg(XSTR); }
  @Override public TVLambda as_lambda() { return (TVLambda)arg(XFUN); }
  
  @Override boolean _unify_err(TV3 that) {
    assert !unified() && !that.unified(); // Do not unify twice
    int x = that.eidx();                  // Which part unifies
    that._deps_work_clear();              // 
    TV3 ecp = that.copy();                // Make a shallow clone of that
    that._uf = this;                      // That is crushed into this
    if( _args[x]==null ) _args[x] = ecp;  // Unify shallow clone into others of its kind
    else ecp._unify(arg(x),false);
    return true;
  }

  void err_msg(String msg) {
  }

  // -------------------------------------------------------------
  @Override void _union_impl(TV3 that) {
    if( !(that instanceof TVErr err) ) {
      arg(that.eidx())._union_impl(that);
    } else {
      throw unimpl();
    }
  }

  @Override boolean _unify_impl(TV3 that ) {
    throw unimpl();
  }
  
  // -------------------------------------------------------------
  @Override int eidx() { throw unimpl(); }

  // Defining type, vs failed unification
  public String toString(Type tdef) {
    if( tdef instanceof TypeStruct ts && _args[XFUN]!=null )
      return "A function is being called, but "+tdef+" is not a function";
    return toString();
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    sb.p("[Cannot unify ");
    for( int i=0; i<XMAX; i++ )
      if( _args[i]!=null )
        _args[i]._str(sb,visit,dups,debug).p(" and ");
    return sb.unchar(5).p("]");
  }

}
