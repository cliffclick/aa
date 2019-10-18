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
  String xstr() { return ((is_dead() || is_copy()) ? "x" : "C")+"allEpi"; } // Self short name
  public CallNode call() { return (CallNode)in(0); }

  @Override public Node ideal(GVNGCM gvn) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;

    CallNode call = call();
    Node cctl = call.ctl();
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    if( tcall.at(0) != Type.CTRL ) return null; // Call not executable
    if( !(tcall.at(1) instanceof TypeFunPtr) ) return null;
    TypeFunPtr tfp = (TypeFunPtr)tcall.at(1);

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    BitsFun fidxs = tfp.fidxs();
    if( _defs._len==2 ) {
      RetNode ret = (RetNode)in(1);
      if( ret.is_copy() )       // FunNode already single-caller and collapsed
        return inline(gvn, ret.ctl(), ret.mem(), ret.val(), ret);
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
    if( gvn.type(fun) == Type.XCTRL ) return null;

    // Arg counts must be compatible
    if( fun.nargs() != call.nargs() )
      return null;

    // Single choice; check no conversions needed
    TypeTuple formals = fun._tf._args;
    for( int i=0; i<call.nargs(); i++ ) {
      if( fun.parm(i)==null ) { // Argument is dead and can be dropped?
        if( gvn.type(call.arg(i)) != Type.XSCALAR )
          call.set_arg_reg(i,gvn.con(Type.XSCALAR),gvn); // Replace with some generic placeholder
      } else {
        Type formal = formals.at(i);
        Type actual = gvn.type(call.arg(i));
        if( actual.isBitShape(formal) == 99 ) return null; // Requires user-specified conversion
      }
    }

    // Check for several trivial cases that can be fully inlined immediately.
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
      return inline(gvn,cctl,cmem,call.arg(((ParmNode)rez)._idx), ret);
    // Check for constant body
    if( gvn.type(rez).is_con() && ctl==fun && cmem == mem)
      return inline(gvn,cctl,cmem,rez,ret);

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
      return inline(gvn,cctl,cmem,gvn.xform(irez),ret); // New exciting replacement for inlined call
    }

    // Always wire caller args into known functions
    return wire(gvn,call,fun,ret);
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds an edge in the Call-Graph.
  // TODO: Leaves the Call in the graph - making the graph "a little odd" - double
  // CTRL users - once for the call, and once for the function being called.
  Node wire( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
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
    if( gvn._opt_mode == 2 ) gvn.add_def(this,ret);
    else                         add_def(     ret);
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
    if( gvn._opt_mode != 2 && fidxs.test(BitsFun.ALL) ) // All functions are possible?
      return TypeTuple.CALL;        // Worse-case result

    // Merge returns from all fidxs, wired or not.  Required during GCP to keep
    // optimistic.  JOIN if above center, merge otherwise.  Wiring the calls
    // gives us a faster lookup, but need to be correct wired or not.
    Bits.Tree<BitsFun> tree = fidxs.tree();
    BitSet bs = tree.plus_kids(fidxs);
    boolean lifting = gvn._opt_mode == 2 && fidxs.above_center();
    Type t = lifting ? TypeTuple.CALL : TypeTuple.XCALL;
    for( int fidx = bs.nextSetBit(0); fidx >= 0; fidx = bs.nextSetBit(fidx+1) ) {
      if( tree.is_parent(fidx) ) continue;   // Will be covered by children
      FunNode fun = FunNode.find_fidx(fidx); // Lookup, even if not wired
      if( fun==null || fun.is_dead() )
        continue; // Can be dead, if the news has not traveled yet
      RetNode ret = fun.ret();
      Type tret = gvn.type(ret); // Type of the return
      t = lifting ? t.join(tret) : t.meet(tret);

      // Make real from virtual CG edges in GCP/Opto by wiring calls.
      if( gvn._opt_mode==2 &&        // Manifesting optimistic virtual edges between caller and callee
          !fidxs.above_center() &&   // Still settling down to possibilities
          !fun.is_forward_ref() &&   // Call is in-error
          fidx >= FunNode.PRIM_CNT ) // Do not wire up primitives, but forever take their default inputs and outputs
        wire(gvn,call,fun,ret);
    }

    return t;
  }

  // Inline the CallNode.  Remove all edges except the results.  This triggers
  // "is_copy()", which in turn will trigger the following ProjNodes to inline.
  private Node inline( GVNGCM gvn, Node ctl, Node mem, Node rez, RetNode ret ) {
    assert _defs._len == 1 || _defs._len==2;   // not wired to several choices
    // Unwire any wired called function
    if( _defs._len == 2 && !ret.is_copy() ) {  // Wired, and called function not already collapsing
      FunNode fun = ret.fun();
      for( int i=0; i<fun._defs._len; i++ ) // Unwire
        if( fun.in(i)==ctl ) gvn.set_def_reg(fun,i,gvn.con(Type.XCTRL));
    }
    // Remove all edges except the inlined results
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
}
