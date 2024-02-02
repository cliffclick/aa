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
  public TVLambda( TV3[] args ) { super(args); }
  // return in slot 0, memory in slot 1, display in slot 2, args in slots 3+
  public TV3 ret () { return arg(0); }
  public TV3 dsp () { return arg(DSP_IDX); }
  public int nargs(){ return _args.length; }
  public TVLambda clr_dsp() { _args[DSP_IDX] = null; return this; }

  @Override public TVLambda as_lambda() { return this; }

  @Override int eidx() { return TVErr.XFUN; }

  //@Override TV3 find_nil() { return this; } // TODO: Push down to each child

  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3) { }

  @Override boolean _unify_impl(TV3 that ) {
    TV3 thsi = this;
    int nargs = nargs(), tnargs = ((TVLambda)that).nargs();
    int i;
    for( i=0; i<Math.min(nargs,tnargs); i++ ) {
      if( _args[i]==null ) { assert that._args[i]==null; continue; }
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
    return ptrue();
  }

  // -------------------------------------------------------------
  // This is fresh, and that._args[i] is missing.  Lambdas with missing arguments
  @Override boolean _fresh_missing_rhs(TV3 that, int i, boolean test) {
    if( test ) return ptrue();
    TVLambda lam = that.as_lambda(); // Invariant when called
    int nargs = lam.nargs();
    assert i>=nargs;
    lam._args = Arrays.copyOf(lam._args,i+1);
    TVErr err = new TVErr();
    err.err("Bad arg count",arg(i),null,test);
    Arrays.fill(lam._args,nargs,lam.nargs(),err);
    arg(i)._fresh_unify(err,false);
    return ptrue();
  }

  // -------------------------------------------------------------
  // Sub-classes specify trial_unify on sub-parts.
  // Check arguments and return
  @Override int _trial_unify_ok_impl( TV3 pat ) {
    TVLambda that = (TVLambda) pat; // Invariant when called
    if( nargs() != that.nargs() ) return 7; // Fails to be equal
    // Check all arguments, including return
    int cmp = 1;
    for( int i=0; i<nargs(); i++ ) {
      if( _args[i] != null ) {
        int acmp = arg(i)._trial_unify_ok(that.arg(i));
        cmp |= acmp;                // Maybe arg makes trial a maybe
        if( cmp == 7 ) return 7;    // Arg failed so trial fails
      }
    }
    return cmp;                   // Trial result
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }

  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    // Compatible escaped fidxs
    BitsFun fidxs = Env.ROOT==null ? BitsFun.EMPTY : Env.ROOT.matching_escaped_fidxs(this,dep);
    if( _may_nil ) fidxs = fidxs.set(0);
    if( _use_nil ) throw TODO();
    Type tfun = ADUPS.get(_uid);
    if( tfun != null ) throw TODO(); // return tfun;  // TODO: Returning recursive flow-type functions
    ADUPS.put(_uid, TypeNil.XSCALAR);
    Type dsp = dsp()!=null && nargs() > DSP_IDX ? dsp()._as_flow(dep) : Type.ALL;
    Type rez = ret()._as_flow(dep);
    return TypeFunPtr.malloc(false,fidxs,nargs(),dsp,rez);
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
      if( _args[i] != null )
        _args[i]._get_dups(visit,dups,debug,prims);
    return dups;
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    sb.p("{ ");
    
    for( int i=DSP_IDX; i<nargs(); i++ ) {
      if( _args[i]==null || (i<=DSP_IDX && _args[i] instanceof TVLeaf && !_args[i].unified()) )
        sb.p("- ");             // Print for leaf display or $dyn
      else
        _args[i]._str(sb,visit,dups,debug,prims).p(' ');
    }
    sb.p("-> ");
    // Return
    _args[0]._str(sb,visit,dups,debug,prims).p(' ');    
    return sb.p("}").p(_may_nil ? "?" : "");
  }

}
