package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;

import static com.cliffc.aa.AA.*;

/** A lambda, higher-order function
 *
 */
public class TVLambda extends TV3 {

  public TVLambda( int nargs, TV3 dsp, TV3 ret ) {
    super(new TV3[nargs]);
    // Slot 0/CTL_IDX is reserved for the return.
    // Slot 1/null
    // Slot 2/DSP_IDX is for the display/self/this argument, optional
    // Slots 3+ are normal arguments past display/self/this
    _args[0] = ret;
    _args[DSP_IDX] = dsp;
    for( int i=ARG_IDX; i<nargs; i++ )
      _args[i] = new TVLeaf();
  }
  // return in slot 0, memory in slot 1, display in slot 2, args in slots 3+
  public TV3 ret () { return arg(0); }
  public TV3 dsp () { return arg(DSP_IDX); }
  public int nargs(){ return len(); }
  public TVLambda clr_dsp() { _args[DSP_IDX] = new TVLeaf(); return this; }

  @Override public TVLambda as_lambda() { return this; }

  @Override int eidx() { return TVErr.XFUN; }

  @Override TV3 find_nil() { return this; } // TODO: Push down to each child

  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3) { }

  @Override boolean _unify_impl(TV3 that ) {
    TV3 thsi = this;
    int nargs = nargs(), tnargs = ((TVLambda)that).nargs();
    int i;
    for( i=0; i<Math.min(nargs,tnargs); i++ ) {
      if( _args[i]==null ) continue;
      thsi.arg( i )._unify( that.arg( i ), false );
      thsi = thsi.find();
      that = that.find();      
    }
    if( nargs != tnargs ) {
      // Make the arg counts align
      if( nargs > tnargs ) that._args = _args;
      // Flag the extra args as errors
      for( ; i<Math.max(nargs,tnargs); i++ )
        that.arg(i)._unify_err("Expected "+tnargs+" but found "+nargs,that,null,false);
    }
    return true;
  }

  // -------------------------------------------------------------
  // This is fresh, and that._args[i] is missing.  Lambdas with missing arguments
  @Override boolean _fresh_missing_rhs(TV3 that, int i, boolean test) {
    if( test ) return true;
    TVLambda lam = that.as_lambda(); // Invariant when called
    int nargs = lam.nargs();
    assert i>=nargs;
    lam._args = Arrays.copyOf(lam._args,i+1);
    TVErr err = new TVErr();
    err.err("Bad arg count",arg(i),null,test);
    Arrays.fill(lam._args,nargs,lam.nargs(),err);
    arg(i)._fresh_unify(err,false);
    return true;
  }

  // -------------------------------------------------------------
  // Sub-classes specify trial_unify on sub-parts.
  // Check arguments, not return nor omem.
  @Override boolean _trial_unify_ok_impl( TV3 tv3 ) {
    TVLambda that = (TVLambda)tv3; // Invariant when called
    if( nargs() != that.nargs() ) return false; // Fails to be equal
    // Check all other arguments
    for( int i=DSP_IDX; i<nargs(); i++ )
      if( !arg(i)._trial_unify_ok(that.arg(i)) )
        return false;           // Arg failed, so trial fails
    return true;                // Unify will work
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }

  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    // Compatible escaped fidxs
    BitsFun fidxs = Env.ROOT.matching_escaped_fidxs(this,dep);
    if( _may_nil ) fidxs = fidxs.set(0);
    if( _use_nil ) throw unimpl();
    Type tfun = ADUPS.get(_uid);
    if( tfun != null ) throw unimpl(); // return tfun;  // TODO: Returning recursive flow-type functions
    ADUPS.put(_uid, TypeNil.XSCALAR);
    Type dsp = nargs() > DSP_IDX ? dsp()._as_flow(dep) : Type.ALL;
    Type rez = ret()._as_flow(dep);
    return TypeFunPtr.makex(false,fidxs,nargs(),dsp,rez);
  }
  @Override void _widen( byte widen ) {
    // widen all args as a 2, widen ret as the incoming widen
    ret().widen(widen,false);
    //omem().widen(widen,false);
    for( int i = DSP_IDX; i<nargs(); i++ )
      arg(i).widen((byte)2,false);
  }
  
  @Override public VBitSet _get_dups_impl(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( debug  ) return super._get_dups_impl(visit,dups,debug,prims);
    // Skip memory contents when printing non-debug
    _args[0]._get_dups(visit,dups,debug,prims); // Return
    for( int i=DSP_IDX; i<nargs(); i++ )        // All arguments
      _args[i]._get_dups(visit,dups,debug,prims);
    return dups;
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    sb.p("{ ");
    for( int i=DSP_IDX; i<nargs(); i++ )
      _args[i]._str(sb,visit,dups,debug,prims).p(' ');
    sb.p("-> ");
    // Return
    _args[0]._str(sb,visit,dups,debug,prims).p(' ');    
    return sb.p("}").p(_may_nil ? "?" : "");
  }

}
