package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;

// See FunNode.  Control is not required; Slot 0 is a function value - can be a
// UnresolvedNode (both Any or All) or a RetNode.  Slots 1+ are for args.
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

// At graph-construction time, assign a unique call-site index to the
// ApplyNode.  Make a RetNode for each possible caller... which implies we have
// the worse-case set of callers handy.... which we do not.  So need an approx
// worse-case caller always.

public class ApplyNode extends Node {
  static private int CNT=1;
  public final int _cidx;       // Call site index
  public ApplyNode( Node... defs ) { super(defs); _cidx = CNT++; }
  @Override String str() { return "apply"; }
  @Override public Node ideal(GVNGCP gvn) {

    // If the function is unresolved, see if we can resolve it now
    if( _defs.at(0) instanceof UnresolvedNode )
      return resolve(gvn,(UnresolvedNode)_defs.at(0));
    
    return null;
  }

  // Toss out choices where any args are not "isa" the call requirements.
  // TODO: this tosses out choices too eagerly: no need to force conversions so quickly
  private Node resolve( GVNGCP gvn, UnresolvedNode unr ) {
    // Actual argument types, in a convenient array format
    Type[] actuals = new Type[_defs._len-1];
    for( int i=1; i<_defs._len; i++ )  actuals[i-1] = gvn.type(_defs.at(i));

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
      if( fargs.length != _defs._len-1 ) continue; // Argument count mismatch
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
      return set_def(0,unr2);
    }
    
    // Single choice; insert actual conversions & replace
    Node ret = ns.at(0);
    Node fun = ret.at(2).at(0);
    Type[] formals = ((TypeFun)gvn.type(fun))._ts._ts;
    for( int i=1; i<_defs._len; i++ ) {
      Type formal = formals[i-1];
      Type actual = actuals[i-1];
      if( !actual.isBitShape(formal) ) {
        PrimNode cvt = PrimNode.convert(_defs.at(i),actual,formal);
        if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
        _defs.set(i,gvn.xform(cvt));
      }
    }
    // upgrade function argument to a constant
    return set_def(0,ret);
  }

  @Override public Type value(GVNGCP gvn) {
    Node ret = _defs.at(0);
    if( !(ret instanceof RetNode) ) return gvn.type(ret).ret();
    // Value is the function return type
    Type tret = gvn.type(ret.at(1));
    if( tret.is_con() ) return tret; // Already determined function body is a constant
    
    // If all args are constant, eval immediately.  Note that the Memory edge
    // will define if a function is "pure" or not; no Memory means must be pure.
    Type[] ts = new Type[_defs._len];
    boolean con=true;
    for( int i=1; i<_defs._len; i++ ) if( !(ts[i] = gvn.type(_defs.at(i))).is_con() ) { con=false; break; }
    if( !con ) return tret;     // Non-constant args, no shortcuts
    // Primitives directly apply
    if( ret.at(1) instanceof PrimNode )
      return ((PrimNode)ret.at(1)).apply(ts);
    
    // Need begin recursive execution - full partial evaluation
    throw AA.unimpl();
  }
}
