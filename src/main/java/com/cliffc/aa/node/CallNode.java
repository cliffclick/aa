package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;

import java.lang.AutoCloseable;

// See FunNode.  Control is not required for an apply but inlining the function
// body will require it; slot 0 is for Control.  Slot 1 is a function value -
// can be a UnresolvedNode (choice/Any of functions) or a RetNode.  Slots 2+
// are for args.
//
// When the UnresolvedNode simplifies to a single RetNode, the Call can inline.
// If the Unr is an 'any' then a bunch of function pointers are allowed here.
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
    Node p_u = _defs.at(1);    // Possible ProjNode or Unresolved

    // If the function is unresolved, see if we can resolve it now
    if( p_u instanceof UnresolvedNode ) {
      UnresolvedNode unr = (UnresolvedNode)p_u;
      Ary<Node> projs = unr.resolve(gvn,this); // List of function choices
      if( projs.isEmpty() )                    // No choices possible
        return new ConNode<>(TypeErr.make(unr.errmsg())); // Fail to top

      if( projs._len>1 ) {       // Multiple choices, but save the reduced Unr
        if( projs._len==unr._defs._len ) return null; // No improvement
        throw AA.unimpl();
        //Node unr2 = new UnresolvedNode(); // Build and return a reduced Unr
        //for( Node ret : projs ) unr2.add_def(ret);
        //return set_def(1,unr2,gvn); // Upgrade Call with smaller choices
      }

      // Single choice; insert actual conversions & replace
      Node proj = projs.at(0);
      FunNode fun = (FunNode)(proj.at(0).at(2)); // Proj->Ret->Fun
      Type[] formals = fun._tf._ts._ts;
      for( int i=0; i<nargs(); i++ ) {
        Type formal = formals[i];
        Type actual = actual(gvn,i);
        if( !actual.isBitShape(formal) ) {
          PrimNode cvt = PrimNode.convert(_defs.at(i+2),actual,formal);
          if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
          set_def(i+2,gvn.xform(cvt),gvn);
        }
      }
      // upgrade function argument to a constant
      return set_def(1,proj,gvn);
    }

    // If the function is fully resolved, inline the call site now.
    // This is NOT inlining the function body, just the call site.
    if( p_u instanceof ProjNode ) {
      RetNode ret = (RetNode)p_u.at(0);
      Node    rez = ret.at(1);
      FunNode fun = (FunNode)ret.at(2);
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
      Node rctrl = gvn.xform(new ProjNode(ret,fun._defs._len-1));
      return new CastNode( rctrl, rez, TypeErr.ANY );
    }

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Node unr = _defs.at(1);
    if( unr instanceof UnresolvedNode )
      return ((UnresolvedNode)unr).retype(gvn,this);

    assert unr instanceof ProjNode;
    // Value is the function return type
    RetNode ret = (RetNode)(unr.at(0)); // Must be a return
    Type tret = gvn.type(ret.at(1));
    if( tret.is_con() ) return tret; // Already determined function body is a constant
    
    // Primitives with all constant args are applied immediately.
    //if( ret.at(1) instanceof PrimNode &&
    //    !(ret.at(1) instanceof RandI64) ) { // TODO: Model RandI64 as having an I/O effect so not pure
    //  // If all args are constant, eval immediately.  Note that the Memory edge
    //  // will define if a function is "pure" or not; no Memory means must be pure.
    //  Type[] ts = new Type[_defs._len-2+1];
    //  boolean con=true;
    //  for( int i=2; i<_defs._len; i++ ) if( !(ts[i-1] = gvn.type(_defs.at(i))).is_con() ) { con=false; break; }
    //  if( con )     // Constant args, apply immediately
    //    return ((PrimNode)ret.at(1)).apply(ts);
    //}
    // TODO: if apply args are all constant, do I partial-eval here or in Ideal?
    return tret;
  }
  

  // Number of actual arguments
  int nargs() { return _defs._len-2; }
  // Actual arguments
  Type actual(GVNGCM gvn, int x) { return gvn.type(actual(x)); }
  private Node actual( int x ) { return _defs.at(x+2); }
  
  // Parser support keeping args alive during parsing; if a syntax exception is
  // thrown while the call args are being built, this will free them all.  Once
  // this hits GVN, it will no longer auto-close.
  @Override public void close() {
    if( !is_dead() && !Env._gvn.touched(this) )
      Env._gvn.kill_new(this);  // Free state on 
  }

  @Override public int hashCode() { return super.hashCode()+_cidx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode apply = (CallNode)o;
    return _cidx==apply._cidx;
  }
}
