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
    Node retx = _defs.at(1);    // Possible RetNode or Unresolved

    // If the function is unresolved, see if we can resolve it now
    if( retx instanceof UnresolvedNode ) {
      Ary<Node> rets = ((UnresolvedNode)retx).resolve(gvn,this);
      // List of function choices

      if( rets.isEmpty() ) // TODO: Return a new ErrNode() which preserves syntax line numbers
        return new ConNode<>(Type.ANY); // Fail to top

      if( rets._len>1 ) {       // Multiple choices, but save the reduced Unr
        if( rets._len==retx._defs._len ) return null; // No improvement
        throw AA.unimpl();
        //Node unr2 = new UnresolvedNode(); // Build and return a reduced Unr
        //for( Node ret : rets ) unr2.add_def(ret);
        //return set_def(1,unr2,gvn); // Upgrade Call with smaller choices
      }

      // Single choice; insert actual conversions & replace
      Node ret = rets.at(0);
      Node fun = ret.at(2).at(0);
      Type[] formals = ((TypeFun)gvn.type(fun))._ts._ts;
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
      return set_def(1,ret,gvn);
    }

    // If the function is fully resolved, inline the call site now.
    // This is NOT inlining the function body, just the call site.
    if( retx instanceof RetNode ) {
      FunNode  fun = (FunNode) retx.at(0);
      Node     rez =           retx.at(1);
      ParmNode rpc = (ParmNode)retx.at(2);

      // Add an input path to all incoming arg ParmNodes from the Call.
      int pcnt=0;               // Assert all parameters found
      for( Node arg : fun._uses ) {
        if( arg.at(0) == fun && arg instanceof ParmNode ) {
          int pidx = ((ParmNode)arg)._idx;
          if( pidx != nargs()+1) {          // No update to the RPC Parm; it is done below
            gvn.add_def(arg,actual(pidx-1));// 1-based on Parm is 2-based on Call's args
            pcnt++;                         // One more arg found
          }
        }
      }
      assert pcnt == nargs(); // All params found and updated at the function head
      gvn.add_def(fun,ctrl); // Add Control for this path
      gvn.add_def(rpc,gvn.con(TypeInt.con(_cidx)));// The RPC for this call
      // A new private return path replaces the Call.
      // TODO: Upgrade the function type for the known arguments.  THIS RetNode
      // is a more strongly-typed function than the generic return.

      // TODO: Not a RetNode; I want the return result from an actual function
      // call with actual args and NOT the generic return result from function
      // def.  The RetNode being made here is intended to pull a single return
      // result from a single function call, and not all possible return
      // results.
        
      // TODO: Combine RootNode and Env hash lookup... so can change what node
      // a name points too.
      
      // TODO: Graph rewrite of "x=3; foo={y->x+y}"
      // 
      // 2_Fun :=  _    0_Root
      // 6_Parm:= 2_Fun __Con_Scalar
      // 4_RPC := 2_Fun __Con_1     
      // 5_Unr := +:Flt  +:Int
      // 3_Call:= 2_Fun 5_Unr __Con_3 6_Parm  // typerr if Scalar is e.g. String
      // 1_Ret := 2_Fun 3_Call 4_RPC  #1
      // foo->1_Ret
      
      // Call of Unr - resolves 3 fine, but type-var unify parm with either I or F.
      // So instead, force inline which requires Fun get cloned:
      //
      // Fun / Parm_Int64 / RPC / Call(+Int,3  ,Int64) / Ret:Int64
      // Fun / Parm_Flt64 / RPC / Call(+Flt,3.0,Flt64) / Ret:Flt64
      // foo-> { Fun_Int64, Fun_Flt64, Fun_Scalar\I\F }

      // Want to allow all e.g. scalars minus int64 minus flt64
      // Want to break foo into 3 functions, those taking int, those taking flt, and all-the-rest

      // 
      
      return new RetNode( fun, rez, rpc, _cidx );
    }

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Node unr = _defs.at(1);
    if( unr instanceof UnresolvedNode )
      return ((UnresolvedNode)unr).retype(gvn,this);
    
    assert unr instanceof RetNode;
    // Value is the function return type
    Node ret = unr;             // Must be a return
    Type tret = gvn.type(ret.at(1));
    if( tret.is_con() ) return tret; // Already determined function body is a constant
    
    // Primitives with all constant args are applied immediately
    if( ret.at(1) instanceof PrimNode ) {
      // If all args are constant, eval immediately.  Note that the Memory edge
      // will define if a function is "pure" or not; no Memory means must be pure.
      Type[] ts = new Type[_defs._len-2+1];
      boolean con=true;
      for( int i=2; i<_defs._len; i++ ) if( !(ts[i-1] = gvn.type(_defs.at(i))).is_con() ) { con=false; break; }
      if( con )     // Constant args, apply immediately
        return ((PrimNode)ret.at(1)).apply(ts);
    }
    // TODO: if apply args are all constant, do I partial-eval here or in Ideal?
    return tret;
  }
  

  // Number of actual arguments
  int nargs() { return _defs._len-2; }
  // Actual arguments
  Type actual(GVNGCM gvn, int x) { return gvn.type(actual(x)); }
  Node actual(int x) { return _defs.at(x+2); }
  
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
