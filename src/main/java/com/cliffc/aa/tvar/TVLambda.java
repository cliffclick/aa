package com.cliffc.aa.tvar;

import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.DSP_IDX;
import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.AA.unimpl;

/** A lambda, higher-order function
 *
 */
public class TVLambda extends TVNilable {

  public TVLambda( int nargs, TV3 dsp, TV3 ret ) {
    super(true,false,new TV3[nargs]);
    // Slot 0/CTL_IDX is reserved for the return.
    // Slot 1/MEM_IDX is unused.
    // Slot 2/DSP_IDX is for the display/self/this argument
    // Slots 3+ are normal arguments past display/self/this
    _args[0] = ret;
    if( nargs>DSP_IDX ) _args[DSP_IDX] = dsp;
    for( int i=ARG_IDX; i<nargs; i++ )
      _args[i] = new TVLeaf();
  }
  // return in slot 0, display in slot 2, args in slots 3+
  public TV3 ret() { return arg(0); }
  public TV3 dsp() { return arg(DSP_IDX); }
  public int nargs() { return len(); }


  // -------------------------------------------------------------
  @Override
  void _union_impl(TV3 that) {
    if( !(that instanceof TVBase base) ) throw unimpl();
    throw unimpl();
  }

  @Override boolean _unify_impl(TV3 that ) {
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
