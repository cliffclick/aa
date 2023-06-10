package com.cliffc.aa.tvar;

import com.cliffc.aa.Parse;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** A type error.  A collection of un-unifiable TV3s
 *
 */
public class TVErr extends TV3 {

  static final int XSTR=0;
  static final int XFUN=1;
  static final int XNIL=2;
  static final int XPTR=3;
  static final int XMEM=4;
  static final int XMAX=5;
  
  // Errors other than structural unify errors.
  public Ary<String> _errs;

  public Parse _bad;
  
  public TVErr() { super(new TV3[XMAX+XMAX]); }

  @Override public TVStruct as_struct() { return (TVStruct)arg(XSTR); }
  @Override public TVLambda as_lambda() { return (TVLambda)arg(XFUN); }
  @Override public TVNil    as_nil   () { return (TVNil   )arg(XNIL); }
  @Override public TVPtr    as_ptr   () { return (TVPtr   )arg(XPTR); }

  @Override int eidx() { throw unimpl(); }

  public TV3 make_struct() {
    assert _args[XSTR]==null;
    return (_args[XSTR] = new TVLeaf());
  }
  
  @Override TV3 find_nil() { return this; }

  // This is Fresh, that is TVErr and missing index i.
  // Fresh copy LHS into RHS.
  @Override boolean _fresh_missing_rhs(TV3 that, int i, boolean test) {
    if( test ) return true;
    assert that instanceof TVErr;
    assert that._args[i]==null;
    that._args[i]= _args[i]._fresh();
    return true;
  }

  // THAT is not an error, unify it with the correct sub-part and union it to
  // THIS error.
  @Override boolean _unify_err(TV3 that) {
    assert !unified() && !that.unified(); // Do not unify twice
    assert !(that instanceof TVErr);
    that._deps_work_clear();              //
    if( !(that instanceof TVLeaf) ) {
      int x = that.eidx();                 // Which part unifies
      if( arg(x)==that ) return false;
      TV3 ecp = that.copy();               // Make a shallow clone of that
      if( _args[x]==null ) _args[x] = ecp; // Unify shallow clone into others of its kind
      else ecp._unify(arg(x),false);
    }
    that._uf = this;            // That is crushed into this
    return true;                // Always progress
  }

  // This is fresh and an Err and that is not.
  @Override boolean _fresh_unify_err(TV3 that, boolean test) {
    assert !unified() && !that.unified(); // Do not unify twice
    assert !(that instanceof TVErr);
    TV3 tv3 = arg(that.eidx());
    if( tv3==null ) {
      if( !test ) _args[that.eidx()] = that;
      return true;
    }
    return tv3._fresh_unify(that,test);
  }
  // This is an Err and that is fresh and not an error
  final boolean _fresh_unify_err_fresh(TV3 that, boolean test) {
    assert !unified() && !that.unified(); // Do not unify twice
    assert !(that instanceof TVErr);
    // Fresh-unify that into the matching error part
    TV3 tv3 = arg(that.eidx());
    if( tv3==null ) {
      if( !test ) _args[that.eidx()] = that;
      return true;
    }
    return that._fresh_unify(tv3,test);
  }

  // Make this tvar an error and add an error message
  @Override public boolean unify_err(String msg, TV3 extra, Parse bad, boolean test) { return false; }
  
  // -------------------------------------------------------------
  // Union/merge subclass specific bits
  @Override public void _union_impl(TV3 that) {
    if( !(that instanceof TVErr terr) ) {
      TV3 err_part = arg(that.eidx());
      if( err_part == null ) _args[that.eidx()] = that;
      else err_part._union_impl(that);
    } else {
      // Merge error messages
      for( String err : terr._errs )
        if( _errs.find(err)== -1 )
          throw unimpl();         // Progress
      for( String err : _errs )
        if( terr._errs.find(err)== -1 )
          throw unimpl();         // Progress
    }
  }

  @Override boolean _unify_impl(TV3 that ) {
    TVErr terr = (TVErr)that;
    for( int i=0; i<XMAX; i++ ) {
      TV3 tv3 = arg(i);
      if( tv3!=null )
        if( terr.arg(i)==null ) terr._args[i] = tv3;
        else tv3._unify(terr.arg(i),false);
    }
    return ptrue();
  }
  
  // -------------------------------------------------------------
  @Override boolean _exact_unify_impl( TV3 tv3 ) { throw unimpl(); }

  // -------------------------------------------------------------
  // If there's exactly one type, we can as_flow it.  Otherwise, ambiguous and
  // not sure what to do.
  @Override Type _as_flow( Node dep ) {
    TV3 tv=null;
    for( TV3 tvar : _args ) {
      if( tvar!=null ) {
        if( tv!=null ) throw unimpl(); // Multi choices; not sure what to do with Type
        tv = tvar.find();
      }
    }
    return tv._as_flow(dep);
  }

  @Override void _widen( byte widen ) {
    for( int i=0; i<_args.length; i++ )
      if( _args[i]!=null )
        arg(i).widen(widen,false);
  }
    
  @Override public TVErr copy() {
    TVErr terr = (TVErr)super.copy();
    terr._errs = _errs.deepCopy();
    return terr;
  }

  // Add an error message
  public boolean err(String err, TV3 extra, Parse bad, boolean test) {
    assert !unified();
    if( err==null ) return false;
    err = err.intern();
    int idx;
    if( _errs!=null && (idx=_errs.find(err))!= -1 ) // Prior error?
      return extra!=null && extra.unify(arg(idx+XMAX),test); // Also progress if unify progresses
    if( test ) return true;
    if( _errs==null ) _errs = new Ary<>(new String[1],0);
    _args[_errs._len+XMAX] = extra;
    _errs.push(err);
    _bad = bad;
    return true;
  }

  // Defining type, vs failed unification
  public String toString(Type tdef) {
    if( tdef instanceof TypeStruct ts && _args[XFUN]!=null )
      return "A function is being called, but "+tdef+" is not a function";
    return toString();
  }

  // Printing errors!
  // Format with no  types: [err0,err1,...]   "Expected 3 args but found 4; expected foo but found bar"
  // Format with one type : [err0 in t0]      "Missing field .y in @{x=3}"
  // Format with 2+  types: [Cannot unify t0 and t1...]
  // Format with 2+  types: [err0, cannot unify t0 and t1...]

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( debug ) sb.p("[");
    if( _errs!=null ) {
      for( int i=0; i<_errs._len; i++ ) {
        String msg = _errs.at(i);
        int idx = msg.indexOf('%');
        if( idx==-1 ) sb.p(msg);
        else {
          sb.p(msg.substring(0,idx));
          _args[i+XMAX]._str(sb,visit,dups,debug,prims);
          sb.p(msg.substring(idx+1));
        }
        sb.p(", ");
      }
      sb.unchar(2);
    }
    int cnt=0; for( int i=0; i<XMAX; i++ ) if( _args[i]!=null ) cnt++;
    if( cnt>0 ) {
      if( cnt>1 ) {
        if( _errs==null ) sb.p("Cannot unify ");
        else sb.p(", cannot unify ");
      } // If exactly 1 choice, assume a prior message has detail info
      for( int i=0; i<XMAX; i++ )
        if( _args[i]!=null )
          _args[i]._str(sb,visit,dups,debug,prims).p(" and ");
      sb.unchar(5);
    }
    if( debug ) sb.p("]");
    return sb;
  }

}
