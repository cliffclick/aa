package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import java.util.BitSet;

// TODO CNC NOTES
// 
// Move Unresolved handling into CallEpi from Call, since it will not wire
// but the result type is more precise.
// 
// ----
// See CallNode.  Slot 0 is the matching Call, which returns a type of its
// input args and function pointer.  The remaining slots are Returns which are
// typed as standard function returns: {Ctrl,Mem,Val}.  These Returns represent
// call-graph edges that are known to be possible, and thus their fidx appears
// in the Call's BitsFun type.
//
// Pre-opto it is possible for the all-functions type to appear at a Call, and
// in this case the CallEpi must assume all possible calls may happen, they are
// just not wired up yet.

public final class CallEpiNode extends Node {
  public CallEpiNode( Node... rets ) { super(OP_CALLEPI,rets); }
  String xstr() { return (is_copy() ? "x" : "C")+"allEpi"; } // Self short name
  public CallNode call() { return (CallNode)in(0); }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;

    CallNode call = call();
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    if( tcall.at(0) != Type.CTRL ) return null; // Call not executable
    if( !(tcall.at(1) instanceof TypeFunPtr) ) return null;
    TypeFunPtr tfp = (TypeFunPtr)tcall.at(1);
    
    // The one allowed function is already wired?  Then directly inline.
    BitsFun fidxs = tfp.fidxs();
    if( _defs._len==2 ) {
      RetNode ret = (RetNode)in(1);
      if( ret.is_copy() || !ret.fun().has_unknown_callers() ) {
        assert ret.is_copy() || ret.fun()._tf.isa(tfp);
        return inline(gvn, ret.ctl(), ret.mem(), ret.val());
      }
    }

    // If the call's allowed functions excludes any wired, remove the extras
    BitSet bs = fidxs.tree().plus_kids(fidxs);
    if( !fidxs.test(BitsFun.ALL) ) {
      for( int i = 1; i < _defs._len; i++ ) {
        RetNode ret = (RetNode) in(i);
        if( !bs.get(ret.fidx()) ) // Wired call is not actually executable?
          // Remove the edge.  Happens after e.g. cloning a function, where
          // both cloned and original versions are wired, but only one is
          // reachable.
          del(i--);
      }
    }

    // If call allows many functions, bail out.
    if( fidxs.is_class() )
      return null; // Multiple fidxs

    // Call allows 1 function not yet wired, sanity check it.
    int fidx = tfp.fidx();
    FunNode fun = FunNode.find_fidx(fidx);
    if( fun.is_forward_ref() ) return null;
    
    // Arg counts must be compatible
    if( fun.nargs() != call.nargs() )
      return null;
    
    // Single choice; check no conversions needed
    TypeTuple formals = fun._tf._args;
    for( int i=0; i<call.nargs(); i++ ) {
      if( fun.parm(i)==null )   // Argument is dead and can be dropped?
        call.set_arg_reg(i,gvn.con(Type.XSCALAR),gvn); // Replace with some generic placeholder
      else {
        Type formal = formals.at(i);
        Type actual = gvn.type(call.arg(i));
        if( actual.isBitShape(formal) == 99 ) return null; // Requires user-specified conversion
      }
    }
    
    // Check for several trivial cases that can be fully inlined immediately.
    Node cctl = call.ctl();
    Node cmem = call.mem();
    RetNode ret = fun.ret();    // Return from function
    Node ctl  = ret.ctl();      // Control being returned
    Node mem  = ret.mem();      // Memory  being returned
    Node rez = ret.val();       // Value   being returned
    // This is due to a shortcut, where we do not modify the types of
    // primitives so they can be reused in tests.  Instead, the primitive is
    // "pure" and the memory is just a pass-through of the Call memory.
    if( gvn.type(mem) == TypeMem.XMEM ) mem = cmem;
    
    // Check for zero-op body (id function)
    if( rez instanceof ParmNode && rez.in(0) == fun && cmem == mem )
      return inline(gvn,cctl,cmem,call.arg(((ParmNode)rez)._idx));
    // Check for constant body
    if( gvn.type(rez).is_con() && ctl==fun )
      return inline(gvn,cctl,cmem,rez);

    // Check for a 1-op body using only constants or parameters and no memory effects
    boolean can_inline=!(rez instanceof ParmNode) && mem==cmem;
    for( Node parm : rez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rez.copy(gvn);// Copy the entire function body
      for( Node parm : rez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? call.arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = call._badargs;
      return inline(gvn,cctl,cmem,gvn.xform(irez)); // New exciting replacement for inlined call
    }
    
    assert fun.in(1)._uid!=0; // Never wire into a primitive, just clone/inline it instead (done just above)
    
    // Always wire caller args into known functions
    return wire(gvn,call,fun,ret);
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds an edge in the Call-Graph.
  // TODO: Leaves the Call in the graph - making the graph "a little odd" - double
  // CTRL users - once for the call, and once for the function being called.
  private Node wire( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
    assert _keep==0;            // not expecting this during calls

    for( int i=1; i<_defs._len; i++ )
      if( in(i) == ret )        // Look for same Ret
        return null;            // Already wired up

    // Make sure we have enough args before wiring up (makes later life easier
    // to assume correct arg counts).  Note that we cannot, in general,
    // type-check the args during GCP, as they will start out too-high and pass
    // any isa-check.  Later, after wiring up in GCP they might fall to an
    // error state - so we have to support having error args coming in.
    int nargs = call.nargs();
    for( Node arg : fun._uses )
      if( arg.in(0) == fun && arg instanceof ParmNode &&
          ((ParmNode)arg)._idx >= nargs )
        return null;            // Wrong arg-count

    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        Node actual = idx==-1 ? gvn.con(TypeRPC.make(call._rpc)) : (idx==-2 ? call.mem() : call.arg(idx));
        gvn.add_def(arg,actual);
      }
    }
    // Add matching control
    gvn.add_def(fun,call.ctl());
    // Add the CallEpi hook
    add_def(ret);
    return this;
  }

  // Merge call-graph edges, but the call-graph is not discovered prior to GCP.
  // If the Call's type includes all-functions, then the CallEpi must assume
  // unwired Returns may yet appear, and be conservative.  Otherwise it can
  // just meet the set of known functions.
  @Override public Type value(GVNGCM gvn) {
    if( is_copy() )             // Already collapsed?  Just echo inputs
      return TypeTuple.make(gvn.type(in(0)),gvn.type(in(1)),gvn.type(in(2)));
    
    CallNode call = call();
    TypeTuple ctt = (TypeTuple)gvn.type(call);
    if( ctt.at(0) == Type.XCTRL ) return TypeTuple.XCALL;
    if( !(ctt.at(1) instanceof TypeFunPtr) )
      return TypeTuple.CALL;
    TypeFunPtr funt = (TypeFunPtr)ctt.at(1);
    BitsFun fidxs = funt.fidxs();
    if( fidxs.test(BitsFun.ALL) ) // All functions are possible?
      return TypeTuple.CALL;        // Worse-case result

    // If there are any fidxs that do not have a matching Return, we must
    // assume it is an unwired call returning the max pessimal result and bail
    // out with TypeTuple.CALL.
    BitSet bs = new BitSet();
    for( int i=1; i<_defs._len; i++ )
      bs.set(((RetNode)_defs.at(i)).fidx());
    for( int fidx : fidxs )
      // FIDXs that are parents got split & cloned... and always both child
      // fidxs get wired, although the parent never shows up wired anymore.  If
      // not a parent and not wired, must be an unwired call returning a max
      // pessimal result.
      if( !fidxs.tree().is_parent(fidx) && !bs.get(fidx) )
        return TypeTuple.CALL;
    
    // If there are any Returns without a matching fidx, we can assume that
    // function is not called and not merge it.
    BitSet bsplus = fidxs.tree().plus_kids(fidxs);
    Type t = TypeTuple.XCALL;
    for( int i=1; i<_defs._len; i++ ) {
      RetNode ret = (RetNode)_defs.at(i);
      if( bsplus.get(ret.fidx()) )     // This function is possible
        t = t.meet(gvn.type(ret)); // So merge his results
    }
    
    return t;
  }

  // Inline the CallNode.  Remove all edges except the results.  This triggers
  // "is_copy()", which in turn will trigger the following ProjNodes to inline.
  private Node inline( GVNGCM gvn, Node ctl, Node mem, Node rez ) {
    add_def(ctl);
    add_def(mem);
    add_def(rez);
    while( _defs._len > 3 ) remove(0,gvn);
    return this;
  }
  // If slot 0 is not a CallNode, we have been inlined.
  private boolean is_copy() { return !(in(0) instanceof CallNode); }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return is_copy() ? in(idx) : null; }
  @Override public Type all_type() { return TypeTuple.CALL; }

  // Check for proper wiring at this call-site.  All wired RetNodes have
  // matching input paths to the Call.  *Types* are not checked, as we might be
  // mid-opto or mid-iter.
  String check() {
    CallNode call = call();
    TypeRPC trpc = TypeRPC.make(call._rpc);
    // Check all wired functions for a matching RPC to this Call.
    for( int i=1; i<_defs._len; i++ ) {
      RetNode ret = (RetNode)in(i); // Wired return
      FunNode fun = ret.fun();      // Wired function
      ParmNode rpcs = fun.rpc();    // Wired RPC
      if( rpcs == null ) return "Missing RPC parm";
      int xpath = -1;
      for( int path=1; path<rpcs._defs._len; path++ ) {
        if( rpcs.in(path) instanceof ConNode &&
            ((ConNode)rpcs.in(path))._t == trpc ) {
          if( xpath != -1 ) return "RPC found twice, once on path "+xpath+" and again on path "+path;
          xpath = path;
        }
      }
      if( xpath == -1 ) return "Wired "+fun+", with RPCS "+rpcs+", but no matching RPC for "+call;
    }
    return null;
  }
  
}
