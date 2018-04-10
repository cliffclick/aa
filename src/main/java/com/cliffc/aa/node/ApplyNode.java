package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;

import java.lang.AutoCloseable;

// See FunNode.  Control is not required for an apply but inlining the function
// body will require it; slot 0 is for Control.  Slot 1 is a function value -
// can be a UnresolvedNode (both Any or All) or a RetNode.  Slots 2+ are for args.
//
// When the UnresolvedNode simplifies to a single RetNode, the Apply can inline.
// If the Unr is an 'all' then a bunch of function pointers are allowed here.
//
// Apply-inlining can happen anytime we have a known function pointer, and
// might be several known function pointers - we are inlining the type analysis
// and not the execution code.  For this kind of inlining we replace the
// ApplyNode with a call-site specific RetNode, move all the ApplyNode args to
// the ParmNodes just like the Fun/Parm is a Region/Phi.  The call-site index
// is just like a ReturnPC value on a real machine; it dictates which of
// several possible returns apply... and can be merged like a PhiNode

public class ApplyNode extends Node implements AutoCloseable {
  static private int CNT=2;     // Call site index; 1 is reserved for unknown callers
  public final int _cidx;       // Call site index; 1 is reserved for unknown callers
  public ApplyNode( Node... defs ) { super(OP_APLY,defs); _cidx = CNT++; }
  @Override String str() { return "apply"; }
  @Override public Node ideal(GVNGCP gvn) {
    Node ctrl = _defs.at(0);    // Control for apply/call-site
    Node ret  = _defs.at(1);    // Possible RetNode

    // If the function is unresolved, see if we can resolve it now
    if( ret instanceof UnresolvedNode )
      return resolve(gvn,(UnresolvedNode)ret);

    // If the function is fully resolved, inline the call site now.
    // This is NOT inlining the function body, just the call site.
    if( ret instanceof RetNode ) {
      FunNode  fun = (FunNode) ret.at(0);
      Node     rez =           ret.at(1);
      ParmNode rpc = (ParmNode)ret.at(2);

      // Add an input path to all incoming arg ParmNodes from the Apply.
      int pcnt=0;               // Assert all parameters found
      for( Node arg : fun._uses ) {
        if( arg.at(0) == fun && arg instanceof ParmNode ) {
          int pidx = ((ParmNode)arg)._idx;
          if( pidx != _defs._len-2 ) {      // No update to the RPC Parm; it is done below
            arg.add_def(_defs.at(pidx + 2));// 0-based on Parm is 2-based on Apply's args
            pcnt++;                         // One more arg found
          }
        }
      }
      assert pcnt == _defs._len-2; // All params found and updated at the function head
      fun.add_def(ctrl);           // Add Control for this path
      rpc.add_def(gvn.con(TypeInt.con(_cidx)));// The RPC for this call
      // A new private return path replaces the Apply.
      // TODO: Upgrade the function type for the known arguments.  THIS RetNode is a more strongly-typed function than the generic return
      return new RetNode( fun, rez, rpc, _cidx );
    }

    return null;
  }

  // Toss out choices where any args are not "isa" the call requirements.
  // TODO: this tosses out choices too eagerly: no need to force conversions so quickly
  private Node resolve( GVNGCP gvn, UnresolvedNode unr ) {
    // Actual argument types, in a convenient array format
    Type[] actuals = new Type[_defs._len-2];
    for( int i=2; i<_defs._len; i++ )  actuals[i-2] = gvn.type(_defs.at(i));

    // Set of possible choices with fewest conversions
    Ary<Node> ns = new Ary<>(new Node[1],0);
    int min_cvts = 999;         // Required conversions
    
    // for each function, see if the actual args isa the formal args.  If not, toss it out.
    outerloop:
    for( int i=0; i<unr._defs._len; i++ ) {
      // Peek Ret->RPC->Fun and get the function type
      Node ret = unr.at(i);
      TypeFun fun = (TypeFun)gvn.type(ret.at(2).at(0));
      Type[] fargs = fun._ts._ts;   // Type of each argument
      if( fargs.length != _defs._len-2 ) continue; // Argument count mismatch
      // Now check if the arguments are compatible at all
      for( int j=0; j<actuals.length; j++ )
        if( !actuals[j].isa(fargs[j]) ) continue outerloop;
      int cvts=0;               // Count required conversions
      for( int j=0; j<actuals.length; j++ )
        if( !actuals[j].isBitShape(fargs[j]) ) cvts++;
      // Save only choices with minimal conversions
      if( cvts < min_cvts ) { min_cvts = cvts; ns.clear(); }
      if( cvts == min_cvts)
        ns.add(ret);            // This is an acceptable choice.
    }

    if( ns.isEmpty() ) // TODO: Return a new ErrNode() which preserves syntax line numbers
      return new ConNode<>(Type.ANY); // Fail to top

    if( ns._len>1 ) {           // Multiple choices, but save the reduced Unr
      if( ns._len==unr._defs._len ) return null; // No improvement
      Node unr2 = new UnresolvedNode();          // Build and return a reduced Unr
      for( Node ret : ns ) unr2.add_def(ret);
      return set_def(1,unr2,gvn);
    }
    
    // Single choice; insert actual conversions & replace
    Node ret = ns.at(0);
    Node fun = ret.at(2).at(0);
    Type[] formals = ((TypeFun)gvn.type(fun))._ts._ts;
    for( int i=2; i<_defs._len; i++ ) {
      Type formal = formals[i-2];
      Type actual = actuals[i-2];
      if( !actual.isBitShape(formal) ) {
        PrimNode cvt = PrimNode.convert(_defs.at(i),actual,formal);
        if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
        set_def(i,gvn.xform(cvt),gvn);
      }
    }
    // upgrade function argument to a constant
    return set_def(1,ret,gvn);
  }

  @Override public Type value(GVNGCP gvn) {
    Node ret = _defs.at(1);
    if( !(ret instanceof RetNode) ) return gvn.type(ret).ret();
    // Value is the function return type
    Type tret = gvn.type(ret.at(1));
    if( tret.is_con() ) return tret; // Already determined function body is a constant
    
    // Primitives with all constant args are applied immediately
    if( ret.at(1) instanceof PrimNode ) {
      // If all args are constant, eval immediately.  Note that the Memory edge
      // will define if a function is "pure" or not; no Memory means must be pure.
      Type[] ts = new Type[_defs._len-1];
      boolean con=true;
      for( int i=2; i<_defs._len; i++ ) if( !(ts[i-1] = gvn.type(_defs.at(i))).is_con() ) { con=false; break; }
      if( con )     // Constant args, apply immediately
        return ((PrimNode)ret.at(1)).apply(ts);
    }
    // TODO: if apply args are all constant, do I partial-eval here or in Ideal?
    return tret;
  }

  // Parser support keeping args alive during parsing; if a syntax exception is
  // thrown while the call args are being built, this will free them all.  Once
  // this hits GVN, it will no longer auto-close.
  @Override public void close() {
    //if( Env._gvn.touched(this) ) return;
    //if( is_dead() ) return; // Already deleted once
    //Env._gvn.kill_new(this);
    throw AA.unimpl(); // too many weirdo cases
  }

  @Override public int hashCode() { return super.hashCode()+_cidx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ApplyNode) ) return false;
    ApplyNode apply = (ApplyNode)o;
    return _cidx==apply._cidx;
  }
}
