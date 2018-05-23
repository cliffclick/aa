package com.cliffc.aa.node;

import com.cliffc.aa.*;

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
// CallNode with a call-site specific Epilog, move all the CallNode args to
// the ParmNodes just like the Fun/Parm is a Region/Phi.  The call-site index
// is just like a ReturnPC value on a real machine; it dictates which of
// several possible returns apply... and can be merged like a PhiNode

public class CallNode extends Node implements AutoCloseable {
  private static int RPC=1; // Call-site return PC
  private final int _rpc;   // Call-site return PC
  private boolean _inlined;
  private Type   _cast_ret;     // Return type has been up-casted
  private Parse  _cast_P;       // Return type cast fail message
  private Parse  _badargs;      // Error for e.g. wrong arg counts or incompatible args
  public CallNode( Parse badargs, Node... defs ) { super(OP_CALL,defs); _rpc=RPC++; _badargs = badargs; }

  String xstr() { return "Call#"+_rpc; } // Self short name
  String  str() { return xstr(); }       // Inline short name
  
  private static int PRIM_RPC; // Primitives count of call-sites
  public static void init0() { PRIM_RPC=RPC; }
  public static void reset_to_init0(GVNGCM gvn) { RPC = PRIM_RPC; }

  @Override public Node is_copy(GVNGCM gvn, int idx) { return _inlined ? at(idx) : null; }

  // Number of actual arguments
  int nargs() { return _defs._len-2; }
  // Actual arguments.
  Node arg( int x ) { return _defs.at(x+2); }
  
  // Parser support keeping args alive during parsing; if a syntax exception is
  // thrown while the call args are being built, this will free them all.  Once
  // this hits GVN, it will no longer auto-close.
  @Override public void close() {
    if( !is_dead() && !Env._gvn.touched(this) )
      Env._gvn.kill_new(this);  // Free state on 
  }

  @Override public Node ideal(GVNGCM gvn) {
    if( skip_ctrl(gvn) ) return this;
    // If an inline is in-progress, no other opts and this node will go dead
    if( _inlined ) return null;
    //// If an upcast is in-progress, no other opts until it finishes
    //if( _cast_ret !=null ) return null;
    //
    Node ctrl = _defs.at(0);    // Control for apply/call-site
    Node unk  = _defs.at(1);    // Function epilog
    //
    //// Type-checking a function; requires 2 steps, one now, one in the
    //// following data Proj from the worklist.
    //if( funv instanceof TypeNode ) {
    //  TypeNode tn = (TypeNode)funv;
    //  TypeFun tf_cast = (TypeFun)tn._t;
    //  set_def(1,tn.at(1),gvn);
    //  for( int i=0; i<nargs(); i++ ) // Insert casts for each parm
    //    set_def(i+2,gvn.xform(new TypeNode(tf_cast._ts.at(i),arg(i),tn._error_parse)),gvn);
    //  _cast_ret = tf_cast._ret;      // Upcast return results
    //  _cast_P = tn._error_parse;     // Upcast failure message
    //  throw AA.unimpl(); // Untested, remove & retry
    //  //return this;
    //}

    // If the function is unresolved, see if we can resolve it now
    if( unk instanceof UnresolvedNode ) {
      Node fun = ((UnresolvedNode)unk).resolve(gvn,this);
      if( fun != null ) { set_def(1,fun,gvn); return this; }
    }

    //// Similarly, if arguments do not match, push TypeNodes "uphill" to get
    //// correct args to the function.  The TypeNodes will push the typing
    //// outward until we hit a direct conflict.
    //boolean did_cast = false;
    //for( int i=0; i<nargs(); i++ ) {
    //  Type formal = t.arg(i);
    //  Type actual = gvn.type(arg(i));
    //  if( !actual.isa(formal) ) {
    //    set_def(i+2,gvn.xform(new TypeNode(formal,arg(i),_badargs)),gvn);
    //    did_cast = true;
    //  }
    //}
    //if( did_cast ) return this;

    // Unknown function(s) being called
    if( !(unk instanceof EpilogNode) )
      return null;
    EpilogNode epi = (EpilogNode)unk;
    Node    rez = epi.val ();
    FunNode fun = epi.fun ();

    // Single choice; insert actual conversions as needed
    Type[] formals = fun._tf._ts._ts;
    for( int i=0; i<nargs(); i++ ) {
      Type formal = formals[i];
      Type actual = gvn.type(arg(i));
      byte xcvt = actual.isBitShape(formal);
      if( xcvt == 99 ) throw AA.unimpl(); // Error cases should not reach here
      if( xcvt == -1 ) return null;       // Wait for call args to resolve
      if( xcvt == 1 ) {
        PrimNode cvt = PrimNode.convert(_defs.at(i+2),actual,formal);
        if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
        set_def(i+2,gvn.xform(cvt),gvn);
      }
    }

    // If this is a forward-ref we have no body to inline
    if( rez == fun ) // TODO: better forward-ref test
      throw AA.unimpl(); // return null;

    // Check for several trivial cases that can be fully inlined immediately.
    // Check for zero-op body (id function)
    if( rez instanceof ParmNode && rez.at(0) == fun ) return inline(gvn,arg(0));
    // Check for constant body
    if( rez instanceof ConNode ) return inline(gvn,rez);

    // Check for a 1-op body using only constants or parameters
    boolean can_inline=true;
    for( Node parm : rez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.at(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rez.copy();   // Copy the entire function body
      for( Node parm : rez._defs )
        irez.add_def((parm instanceof ParmNode && parm.at(0) == fun) ? arg(((ParmNode)parm)._idx) : parm);
      return inline(gvn,gvn.xform(irez));  // New exciting replacement for inlined call
    }

    // If this is a primitive, we never change the function header via inlining the call
    assert fun.at(1)._uid!=0;

    // Inline the call site now.
    // This is NOT inlining the function body, just the call site.
    assert fun._tf._ts._ts.length == nargs();
    // Add an input path to all incoming arg ParmNodes from the Call.
    int pcnt=0;               // Assert all parameters found
    for( Node arg : fun._uses ) {
      if( arg.at(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        Node actual = idx==-1 ? gvn.con(TypeRPC.make(_rpc)) : arg(idx);
        gvn.add_def(arg,actual);
        pcnt++;                      // One more arg found
      }
    }
    assert pcnt == nargs()+1; // All params (and rpc) found and updated at the function head
    gvn.add_def(fun,ctrl); // Add Control for this path

    // Flag the Call as is_copy;
    // Proj#0 is RPC to return from the function back to here.
    // Proj#1 is a new CastNode on the tf._ret to regain precision
    // All other slots are killed.
    for( int i=2; i<_defs._len; i++ ) set_def(i,null,gvn);
    Node rpc = gvn.xform(new RPCNode(epi,epi,_rpc));
    set_def(0,rpc,gvn);
    // TODO: Use actual arg types to regain precision
    return inline(gvn,gvn.xform(new CastNode(rpc,epi,fun._tf._ret)));
  }

  // Inline to this Node.
  private Node inline( GVNGCM gvn, Node rez ) {
    gvn.add_work(at(0));        // Major graph shrinkage; retry parent as well
    set_def(1,rez,gvn);
    _inlined = true;            // Allow data projection to find new body
    return this;
  }

  @Override public Type value(GVNGCM gvn) {
    Type t = value0(gvn);
    // Return {control,value} tuple.
    return TypeTuple.make(gvn.type(at(0)),t);
  }
  private Type value0(GVNGCM gvn) {
    Node fun = _defs.at(1);
    Type t = gvn.type(fun);
    if( _inlined ) return t;
    if( t instanceof TypeErr ) return t;
    assert t.is_fun_ptr();
    TypeTuple tepi = (TypeTuple)t;
    Type    tctrl=         tepi.at(0);
    Type    tval =         tepi.at(1);
    TypeRPC trpc =(TypeRPC)tepi.at(2);
    TypeFun tfun =(TypeFun)tepi.at(3);
    assert tctrl==Type.CONTROL;     // Function will never return?
    assert trpc._rpcs.test(_rpc);   // Function knows we are calling it
    if( tfun.nargs() != nargs() )
      return TypeErr.make(_badargs.errMsg("Passing "+nargs()+" arguments to "+tfun+" which takes "+tfun.nargs()+" arguments"));
    // TODO: optimize for Unresolved
    
    // Cannot return the functions return type, unless all args are compatible
    // with the function(s).  Arg-check.
    Type[] formals = tfun._ts._ts;   // Type of each argument
    // Now check if the arguments are compatible at all
    for( int j=0; j<formals.length; j++ ) {
      Type actual = gvn.type(arg(j));
      if( actual instanceof TypeErr ) // Actual is an error, so call result is the same error
        return actual;        // TODO: Actually need to keep all such errors...
      if( !actual.isa(formals[j]) ) { // Actual is not a formal; join of ALL
        String s = actual.is_forward_ref() // Forward/unknown refs as args to a call report their own error
          ? _badargs.forward_ref_err(FunNode.name(((TypeTuple)actual).get_fun().fidx()))
          : _badargs.errMsg("Argument mismatch");
        return TypeErr.make(s);
      }
    }
    return tfun.ret();
  }

  // Called from the data proj.  Return a TypeNode with proper casting on return result.
  TypeNode upcast_return(GVNGCM gvn) {
    Type t = _cast_ret;
    if( t==null ) return null;  // No cast-in-progress
    _cast_ret = null;           // Gonna upcast the return result now
    gvn.add_work(this);         // Revisit after the data-proj cleans out
    return new TypeNode(t,null,_cast_P);
  }

  // Function return type for resolved functions.  Crash/ALL for no functions
  // allowed, join of possible returns otherwise - we get to choose the best
  // choice here.  Errors poison return results.
  private Type retype( GVNGCM gvn, TypeUnion tu ) {
    if( !tu._any ) throw AA.unimpl();
    Type t = TypeErr.ALL;
    for( Type tft : tu._ts._ts ) {
      Type x = retype(gvn,(TypeFun)tft);
      if( x!=null )             // Argument mismatch; join of ALL
        t = t.join(x);          // Join of all
    }
    return t!=TypeErr.ALL ? t : TypeErr.make(_badargs.errMsg("Argument mismatch in call to "+tu.errMsg()));
  }  
  private Type retype( GVNGCM gvn, TypeFun tf ) {
    Type[] formals = tf._ts._ts;   // Type of each argument
    if( formals.length != nargs() ) return null; // Argument count mismatch; join of ALL
    // Now check if the arguments are compatible at all
    for( int j=0; j<formals.length; j++ ) {
      Type actual = gvn.type(arg(j));
      if( actual instanceof TypeErr )
        // Actual is an error, so call result is the same error
        return actual;        // TODO: Actually need to keep all such errors...
      if( !actual.isa(formals[j]) )  // Actual is not a formal; join of ALL
        //return actual.forward_ref() ? TypeErr.make(_badargs.errMsg(((TypeFun)actual).forward_ref_err())) : null;
        throw AA.unimpl();
    }
    return tf.ret();
  }

  // Type of arguments, as a tuple
  //public TypeTuple args(GVNGCM gvn) {
  //  Type[] ts = new Type[nargs()];
  //  for( int i=0; i<nargs(); i++ )
  //    ts[i] = gvn.type(arg(i));
  //  return TypeTuple.make(ts);
  //}

  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }

}

