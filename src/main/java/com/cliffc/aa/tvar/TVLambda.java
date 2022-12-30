package com.cliffc.aa.tvar;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.AA.DSP_IDX;

/** A lambda, higher-order function
 *
 */
public class TVLambda extends TV3 {

  public TVLambda( int nargs, TV3 dsp, TV3 ret ) {
    super(true,new TV3[nargs]);
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
  @Override void _union_impl( TV3 tv3) {
    //assert _uid > tv3._uid;
    // No subparts to union
  }

  @Override boolean _unify_impl(TV3 tv3 ) {
    TVLambda that = (TVLambda)tv3; // Invariant when called
    ret()._unify(that.ret(),false);
    int nargs = nargs(), tnargs = that.nargs();
    for( int i=DSP_IDX; i<Math.min(nargs,tnargs); i++ )
      arg(i)._unify(that.arg(i),false);
    if( nargs != tnargs )
      that.err("Expected "+tnargs+" but found "+nargs);
    return true;
  }

  // Sub-classes specify trial_unify on sub-parts.
  // Check arguments, not return.
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVLambda that = (TVLambda)tv3; // Invariant when called
    if( nargs() != that.nargs() ) return false; // Fails to be equal
    for( int i=DSP_IDX; i<nargs(); i++ )
      if( !arg(i)._trial_unify_ok(that.arg(i), extras) )
        return false;           // Arg failed, so trial fails
    return true;                // Unify will work
  }

  @Override int eidx() { return TVErr.XFUN; }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    sb.p("{ ");
    for( int i=1; i<_args.length; i++ )
      if( _args[i]!=null )
        _args[i]._str(sb,visit,dups,debug).p(' ');
    return _args[0]._str(sb.p("-> "),visit,dups,debug).p(" }").p(_may_nil ? "?" : "");
  }

}
