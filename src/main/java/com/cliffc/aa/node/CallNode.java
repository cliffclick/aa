package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;

import java.lang.AutoCloseable;

// See FunNode.  Control is not required for an apply but inlining the function
// body will require it; slot 0 is for Control.  Slot 1 is a function value - a
// ConNode with a TypeFun or a TypeUnion of TypeFuns.  Slots 2+ are for args.
//
// When the ConNode simplifies to a single TypeFun, the Call can inline.
// Otherwise the TypeUnion lists a bunch of function pointers are allowed here.
//
// Call-inlining can happen anytime we have a known function pointer, and
// might be several known function pointers - we are inlining the type analysis
// and not the execution code.  For this kind of inlining we replace the
// CallNode with a call-site specific RetNode, move all the CallNode args to
// the ParmNodes just like the Fun/Parm is a Region/Phi.  The call-site index
// is just like a ReturnPC value on a real machine; it dictates which of
// several possible returns apply... and can be merged like a PhiNode

public class CallNode extends Node implements AutoCloseable {
  static private int CNT=2;     // Call site index; 1 is reserved for unknown callers
  private final int _cidx;       // Call site index; 1 is reserved for unknown callers
  public CallNode( Node... defs ) { super(OP_CALL,defs); _cidx = CNT++; }
  @Override String str() { return "call"; }
  @Override public Node ideal(GVNGCM gvn) {
    Node ctrl = _defs.at(0);    // Control for apply/call-site
    Node funv = _defs.at(1);    // Function value
    Type t = gvn.type(funv);    // 

    // If the function is unresolved, see if we can resolve it now
    if( t instanceof TypeUnion ) {
      TypeUnion tu = (TypeUnion)t;
      Ary<TypeFun> funs = resolve(tu,gvn); // List of function choices
      if( funs.isEmpty() )                           // No choices possible
        return new ConNode<>(TypeErr.make("Argument mismatch in call to "+tu.errMsg())); // Fail to top
      if( funs._len>1 ) {       // Multiple choices, but save the reduced Unr
        if( funs._len==tu._ts._ts.length ) return null; // No improvement
        throw AA.unimpl();
        //Node unr2 = new ConNode(); // Build and return a reduced Con
        //for( Node ret : projs ) unr2.add_def(ret);
        //return set_def(1,unr2,gvn); // Upgrade Call with smaller choices
      }
      t = funs.at(0);           // Single function choice
    }

    if( !(t instanceof TypeFun) ) {
      throw AA.unimpl();        // untested?
      //return null;
    }

    // Single choice; insert actual conversions & replace
    ProjNode proj = (ProjNode)FunNode.FUNS.at(((TypeFun)t).fidx());
    RetNode ret = (RetNode)proj.at(0);
    FunNode fun = (FunNode)ret .at(2); // Proj->Ret->Fun
    Type[] formals = fun._tf._ts._ts;
    for( int i=0; i<nargs(); i++ ) {
      Type formal = formals[i];
      Type actual = gvn.type(actual(i));
      byte xcvt = actual.isBitShape(formal);
      if( xcvt == 99 ) throw AA.unimpl(); // Error cases should not reach here
      if( xcvt == -1 ) return null;       // Wait for call args to resolve
      if( xcvt == 1 ) {
        PrimNode cvt = PrimNode.convert(_defs.at(i+2),actual,formal);
        if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
        set_def(i+2,gvn.xform(cvt),gvn);
      }
    }

    // Inline the call site now.
    // This is NOT inlining the function body, just the call site.
    Node    rez = ret.at(1);
    if( fun._tf._ts._ts.length != _defs._len-2 ) {
      throw AA.unimpl(); // untested?
      //return null; // Incorrect argument count
    }
    // Add an input path to all incoming arg ParmNodes from the Call.
    int pcnt=0;               // Assert all parameters found
    for( Node arg : fun._uses ) {
      if( arg.at(0) == fun && arg instanceof ParmNode ) {
        int pidx = ((ParmNode)arg)._idx;
        gvn.add_def(arg,actual(pidx-1));// 1-based on Parm is 2-based on Call's args
        pcnt++;                         // One more arg found
      }
    }
    assert pcnt == nargs(); // All params found and updated at the function head
    gvn.add_def(fun,ctrl); // Add Control for this path
    
    // TODO: Big Decision: Calls, when inlined, pass control from the called
    // function, OR from the dominating point: where the function was called.
    // Doing it local from the function preserves a local CFG.
    // Doing it global from the dominating point leads to data calcs with
    // embedded control - but only a post-dominating data-use, no control-use.
    // I.e., a non-CFG control structure.
    
    // TODO: Currently stuck because cannot inline, because Call has dominating
    // (non-local) control
    
    Node rctrl = gvn.xform(new ProjNode(ret,fun._defs._len-1));
    return new CastNode( rctrl, rez, Type.SCALAR );
  }

  @Override public Type value(GVNGCM gvn) {
    Node con = _defs.at(1);
    Type t = gvn.type(con);
    if( t instanceof TypeUnion )
      // Note that this is NOT the same as just a join-over-returns.
      // Error arguments to calls poison the return results.
      return retype(gvn,(TypeUnion)t);
    if( t instanceof TypeFun )
      return ((TypeFun)t)._ret;
    throw AA.unimpl();
    //assert con instanceof ProjNode;
    //RetNode ret = (RetNode)(unr.at(0)); // Must be a return
    //FunNode fun = (FunNode)ret.at(2);
    //if( fun._tf._ts._ts.length != _defs._len-2 )
    //  return TypeErr.make("Function "+fun._tf+" expects "+fun._tf._ts._ts.length+" args but passed "+(_defs._len-2));
    //
    //// Value is the function return type
    //Type tret = gvn.type(ret.at(1));
    //if( tret.is_con() ) return tret; // Already determined function body is a constant
    //
    //// TODO: if apply args are all constant, do I partial-eval here or in Ideal?
    //return tret;
  }
  

  // Number of actual arguments
  private int nargs() { return _defs._len-2; }
  // Actual arguments
  private Node actual( int x ) { return _defs.at(x+2); }
  
  // Parser support keeping args alive during parsing; if a syntax exception is
  // thrown while the call args are being built, this will free them all.  Once
  // this hits GVN, it will no longer auto-close.
  @Override public void close() {
    if( !is_dead() && !Env._gvn.touched(this) )
      Env._gvn.kill_new(this);  // Free state on 
  }

  @Override public Type all_type() { return Type.SCALAR; }
  @Override public int hashCode() { return super.hashCode()+_cidx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode apply = (CallNode)o;
    return _cidx==apply._cidx;
  }

  // Given a list of actuals, apply them to each function choice.  If any
  // (!actual-isa-formal), then that function does not work and supplies an
  // ALL to the JOIN.  This is common for non-inlined calls where the unknown
  // arguments are approximated as SCALAR.  Lossless conversions are allowed as
  // part of a valid isa test.  As soon as some function returns something
  // other than ALL (because args apply), it supercedes other choices- which
  // can be dropped.

  // If more than one choice applies, then the choice with fewest costly
  // conversions are kept; if there is more than one then the join of them is
  // kept - and the program is not-yet type correct (ambiguous choices).
  private Ary<TypeFun> resolve( TypeUnion tu, GVNGCM gvn ) {
    // Set of possible choices with fewest conversions
    Ary<TypeFun> ns = new Ary<>(new TypeFun[1],0);
    int min_cvts = 999;         // Required conversions
    int cvts[] = new int[_defs._len];

    // For each function, see if the actual args isa the formal args.  If not,
    // toss it out.  Also count conversions, and keep the minimal conversion
    // function with all arguments known.
    outerloop:
    for( Type tft : tu._ts._ts ) {
      TypeFun fun = (TypeFun)tft;
      Type[] formals = fun._ts._ts;   // Type of each argument
      if( formals.length != nargs() )
        continue; // Argument count mismatch, toss out this choice
      // Now check if the arguments are compatible at all, keeping lowest cost
      int xcvts = 0;             // Count of conversions required
      boolean unk = false;       // Unknown arg might be incompatible or free to convert
      for( int j=0; j<formals.length; j++ ) {
        Type actual = gvn.type(actual(j));
        Type tx = actual.join(formals[j]);
        if( tx.above_center() ) // Actual and formal have values in common?
          continue outerloop;   // No, this function will never work; e.g. cannot cast 1.2 as any integer
        byte cvt = actual.isBitShape(formals[j]); // +1 needs convert, 0 no-cost convert, -1 unknown, 99 never
        if( cvt == 99 )         // Happens if actual is e.g. TypeErr
          continue outerloop;   // No, this function will never work
        if( cvt == -1 ) unk = true; // Unknown yet
        else xcvts += cvt;          // Count conversions
      }
      if( !unk && xcvts < min_cvts ) min_cvts = xcvts; // Keep minimal known conversion
      cvts[ns._len] = xcvts;    // Keep count of conversions
      ns.add(fun);              // This is an acceptable choice, so far (args can be made to work)
    }
    // Toss out choices with strictly more conversions than the minimal
    for( int i=0; i<ns._len; i++ )
      if( cvts[i] > min_cvts ) {
        cvts[i] = cvts[ns._len-1];
        ns.del(i--);
      }
    return ns;
  }


  
  // Function return type for resolved functions.  Crash/ALL for no functions
  // allowed, join of possible returns otherwise - we get to choose the best
  // choice here.  Errors poison return results.
  private Type retype( GVNGCM gvn, TypeUnion tu ) {
    if( !tu._any ) throw AA.unimpl();
    Type t = Type.SCALAR;
    outerloop:
    for( Type tft : tu._ts._ts ) {
      TypeFun tf = (TypeFun)tft;
      Type[] formals = tf._ts._ts;   // Type of each argument
      if( formals.length != nargs() ) continue; // Argument count mismatch; join of ALL
      // Now check if the arguments are compatible at all
      for( int j=0; j<formals.length; j++ ) {
        Type actual = gvn.type(actual(j));
        if( actual instanceof TypeErr && !t.above_center() )
          // Actual is an error, so call result is the same error
          return actual;        // TODO: Actually need to keep all such errors...
        if( !actual.isa(formals[j]) )
          continue outerloop;   // Actual is not a formal; join of ALL
      }
      t = t.join(tf.ret());
    }
    return t;
  }  
}
