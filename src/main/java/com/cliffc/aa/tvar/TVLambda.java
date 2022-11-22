package com.cliffc.aa.tvar;

import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** A lambda, higher-order function
 *
 */
public class TVLambda extends TVNilable {

  public TVLambda( int nargs ) { super(true,false,make_fun(nargs)); }
  private static TV3[] make_fun(int nargs) {
    TV3[] tvs = new TV3[nargs+1];
    for( int i=0; i<nargs; i++ )
      tvs[i+1] = new TVLeaf();
    return tvs;
  }
  // Used during recursive initial setup
  public void set_ret( TV3 ret ) { assert _args[0]==null; _args[0]=ret; }
  // return in slot 0, display in slot 1, args in slots 2+
  public TV3 ret() { return _find(0); }
  public TV3 dsp() { return arg(0); }  // Display is arg0
  public TV3 arg(int argn) { return _find(argn+1); } // Args are 1-based to skip return


  // -------------------------------------------------------------
  @Override void _union_impl(TV3 that) {
    if( !(that instanceof TVBase base) ) throw unimpl();
    throw unimpl();
  }

  @Override boolean _unify_impl(TV3 that, boolean test ) {
    throw unimpl();
  }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    sb.p("{ ");
    for( int i=1; i<_args.length; i++ )
      if( _args[i]!=null )
        _args[i]._str(sb,visit,dups,debug).p(' ');
    return _args[0]._str(sb.p("-> "),visit,dups,debug).p(" }").p(_may_nil ? "?" : "");
  }

}
