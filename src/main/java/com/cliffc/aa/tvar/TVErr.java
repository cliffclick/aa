package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
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
  static final int XINT=2;
  static final int XFLT=3;
  static final int XCLZ=4;
  static final int XNIL=5;
  static final int XMAX=6;

  public TVErr() { super(false,new TV3[XMAX]); }

  @Override public TVStruct as_struct() { return (TVStruct)arg(XSTR); }
  @Override public TVLambda as_lambda() { return (TVLambda)arg(XFUN); }
  @Override public TVClz    as_clz   () { return (TVClz   )arg(XCLZ); }
  @Override public TVNil    as_nil   () { return (TVNil   )arg(XNIL); }

  public void set_struct( TVStruct st ) { assert _args[XSTR]==null; _args[XSTR] = st; }
  @Override int eidx() { throw unimpl(); }

  @Override TV3 find_nil(TVNil nil) { return this; }

  // This is Fresh, that is TVErr and missing index i.
  // Fresh copy LHS into RHS.
  @Override boolean _fresh_missing_rhs(TV3 that, int i, boolean test) {
    if( test ) return true;
    assert that instanceof TVErr;
    assert that._args[i]==null;
    that._args[i]= _args[i]._fresh();
    return true;
  }

  @Override boolean _unify_err(TV3 that) {
    assert !unified() && !that.unified(); // Do not unify twice
    assert !(that instanceof TVErr);
    int x = that.eidx();                  // Which part unifies
    that._deps_work_clear();              // 
    TV3 ecp = that.copy();                // Make a shallow clone of that
    that._uf = this;                      // That is crushed into this
    if( _args[x]==null ) _args[x] = ecp;  // Unify shallow clone into others of its kind
    else ecp._unify(arg(x),false);
    return true;
  }

  // This is fresh and an Err and that is not.
  @Override boolean _fresh_unify_err(TV3 that) {
    assert !unified() && !that.unified(); // Do not unify twice
    assert !(that instanceof TVErr);
    TVErr terr = new TVErr();
    terr._unify_err(that);
    _fresh_unify(terr,false);
    return true;    
  }
  // This is an Err and that is fresh and not an error
  boolean _fresh_unify_err_fresh(TV3 that) {
    assert !unified() && !that.unified(); // Do not unify twice
    assert !(that instanceof TVErr);
    throw unimpl();
  }

  public void err_msg(String msg) {
  }

  // -------------------------------------------------------------
  @Override void _union_impl(TV3 that) {
    if( !(that instanceof TVErr err) ) {
      TV3 err_part = arg(that.eidx());
      if( err_part != null )
        err_part._union_impl(that);
    } else {
      throw unimpl();
    }
  }

  @Override boolean _unify_impl(TV3 that ) {
    throw unimpl();
  }
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { throw unimpl(); }
  
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
