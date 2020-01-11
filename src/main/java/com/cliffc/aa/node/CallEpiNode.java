package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import java.util.BitSet;

// See CallNode.  Slot 0 is call-control; slot 1 is call function pointer.  The
// remaining slots are Returns which are typed as standard function returns:
// {Ctrl,Mem,Val}.  These Returns represent call-graph edges that are known to
// be possible and thus their fidx appears in the Call's BitsFun type.
//
// Pre-opto it is possible for the all-functions type to appear at a Call, and
// in this case the CallEpi must assume all possible calls may happen, they are
// just not wired up yet.

public final class CallEpiNode extends Node {
  public CallEpiNode( CallNode call ) { super(OP_CALLEPI,call); }
  public CallEpiNode( Node... nodes ) { super(OP_CALLEPI,nodes); }
  String xstr() { return ((is_dead() || is_copy()) ? "x" : "C")+"allEpi"; } // Self short name
  public CallNode call() { return (CallNode)in(0); }
  int nwired() { return _defs._len-1; }
  int wire_num(int x) { return x+1; }
  RetNode wired(int x) { return (RetNode)in(x+1); }

  @Override public Node ideal(GVNGCM gvn) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;

    CallNode call = call();
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    if( tcall.at(0) != Type.CTRL ) return null; // Call not executable
    Type tfptr = tcall.at(1);
    if( !(tfptr instanceof TypeFunPtr) ) return null; // No known function pointer
    TypeFunPtr tfp = (TypeFunPtr)tfptr;

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    BitsFun fidxs = tfp.fidxs();
    if( nwired()==1 && fidxs.abit() != -1 ) { // Wired to 1 target
      RetNode ret = wired(0);                 // One wired return
      if( ret.fun()._defs._len==2 ) {         // Function is only called by 1 (and not the unknown caller)
        assert ret.fun().in(1).in(0)==call;   // Just called by us
        return inline(gvn, call, ret.ctl(), ret.mem(), ret.val(), ret);
      }
    }

    // If the call's allowed functions excludes any wired, remove the extras
    BitSet bs = fidxs.tree().plus_kids(fidxs);
    if( !fidxs.test(BitsFun.ALL) ) {
      for( int i = 0; i < nwired(); i++ ) {
        RetNode ret = wired(i);
        if( !bs.get(ret.fidx()) ) // Wired call is not actually executable?
          // Remove the edge.  Happens after e.g. cloning a function, where
          // both cloned and original versions are wired, but only one is
          // reachable.
          del(wire_num(i--));
      }
    }

    // If call allows many functions, bail out.
    if( fidxs.is_class() )
      return null; // Multiple fidxs

    // Call allows 1 function not yet wired, sanity check it.
    int fidx = tfp.fidx();
    FunNode fun = FunNode.find_fidx(fidx);
    if( fun.is_forward_ref() || fun.is_dead() ) return null;
    if( gvn.type(fun) == Type.XCTRL ) return null;

    // Arg counts must be compatible
    if( fun.nargs() != call.nargs() )
      return null;

    // Single choice; check no conversions needed
    TypeStruct formals = fun._tf._args;
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
    Node cctl = call.ctl();
    Node cmem = call.mem();
    RetNode ret = fun.ret();    // Return from function
    Node rctl = ret.ctl();      // Control being returned
    Node rmem = ret.mem();      // Memory  being returned
    Node rrez = ret.val();      // Value   being returned
    // If the function does nothing with memory, then use the call memory directly.
    if( rmem instanceof ParmNode && rmem.in(0) == fun )
      rmem = cmem;

    // Check for zero-op body (id function)
    if( rrez instanceof ParmNode && rrez.in(0) == fun && cmem == rmem )
      return inline(gvn,call,cctl,cmem,call.arg(((ParmNode)rrez)._idx), ret);
    // Check for constant body
    if( gvn.type(rrez).is_con() && rctl==fun && cmem == rmem)
      return inline(gvn,call,cctl,cmem,rrez,ret);

    // Check for a 1-op body using only constants or parameters and no memory effects
    boolean can_inline=!(rrez instanceof ParmNode) && rmem==cmem;
    for( Node parm : rrez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( fun.noinline() ) can_inline=false;
    if( can_inline ) {
      Node irez = rrez.copy(false,this,gvn);// Copy the entire function body
      for( Node parm : rrez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? call.arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = call._badargs;
      return inline(gvn,call,cctl,cmem,gvn.xform(irez),ret); // New exciting replacement for inlined call
    }

    // Always wire caller args into known functions
    return wire(gvn,call,fun,ret);
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds an edge in the Call-Graph.
  Node wire( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
    assert _keep==0;            // not expecting this during calls

    for( int i=0; i<nwired(); i++ )
      if( wired(i) == ret )     // Look for same Ret
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
        Node actual = idx==-1 ? gvn.con(TypeRPC.make(call._rpc)) :
          gvn.xform(idx==-2 ? new MProjNode(call,2) : new ProjNode(call,idx+3));
        gvn.add_def(arg,actual);
      }
    }
    // Add matching control to function
    gvn.add_def(fun,gvn.xform(new CProjNode(call,0)));
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
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    if( tcall.at(0) != Type.CTRL ) return TypeTuple.XCALL;
    Type tfptr = tcall.at(1);
    TypeMem call_mem = (TypeMem)tcall.at(2);
    if( !(tfptr instanceof TypeFunPtr) )
      return TypeTuple.CALL;
    TypeFunPtr funt = (TypeFunPtr)tfptr;
    BitsFun fidxs = funt.fidxs();
    if( fidxs.test(BitsFun.ALL) ) // All functions are possible?
      return TypeTuple.CALL;      // Worse-case result
    // If we fall from choice-functions to the empty set of called functions, freeze our output.
    // We might fall past empty and get a valid set.  Probably wrong; if we ever see a
    // choice set of functions, we should not execute.
    if( fidxs.is_empty() ) return gvn.self_type(this);

    // Merge returns from all fidxs, wired or not.  Required during GCP to keep
    // optimistic.  JOIN if above center, merge otherwise.  Wiring the calls
    // gives us a faster lookup, but need to be correct wired or not.

    // Gather the set of aliases passed into the function.
    BitsAlias call_aliases = call_mem.aliases();
    // Set of all possible target functions
    Bits.Tree<BitsFun> tree = fidxs.tree();
    BitSet bs = tree.plus_kids(fidxs);
    // Lifting or dropping Unresolved calls
    boolean lifting = gvn._opt_mode==2;
    Type t = lifting ? TypeTuple.CALL : TypeTuple.XCALL;
    for( int fidx = bs.nextSetBit(0); fidx >= 0; fidx = bs.nextSetBit(fidx+1) ) {
      if( tree.is_parent(fidx) ) continue;   // Will be covered by children
      FunNode fun = FunNode.find_fidx(fidx); // Lookup, even if not wired
      if( fun==null || fun.is_dead() )
        continue;              // Can be dead, if the news has not traveled yet
      if( fun.nargs() != call.nargs() ) // This call-path has wrong args, is in-error for this function
        // Cannot just ignore/continue because the remaining functions might
        // allow the call site to produce a constant and optimize away.
        return TypeTuple.CALL; // No good result until the input function is sensible
      RetNode ret = fun.ret();
      TypeTuple tret = (TypeTuple)gvn.type(ret); // Type of the return
      // Lift the returned memory to be no more than what is available at the
      // call entry plus the function closures - specifically not all the
      // memory from unrelated calls to this same function.
      TypeMem ret_mem_untrimmed = ((TypeMem)tret.at(1));

      // Memory from the function.  Includes memory from other call sites.
      BitsAlias ret_aliases = ret_mem_untrimmed.aliases();

      // Trim to aliases available from this call path.
      //BitsAlias call_trimmed = (BitsAlias)ret_aliases.join(call_aliases);
      // TODO: locals includes what is reachable from the return pointer not
      // all local closures.
      //BitsAlias plus_local = call_trimmed.meet(fun._closure_aliases);
      BitsAlias plus_local = ret_aliases;
      // Strip out primitive memory, since it is never read nor written
      plus_local = plus_local.clear(Env.STK_0._alias);

      // Trim return memory to what is possible on this path.
      TypeMem ret_mem_trimmed = ret_mem_untrimmed.trim_to_alias(plus_local);
      // Because GCP does not reset primitive types, including primitive memory,
      // if this is a primitive, act "as if" it defines the empty memory.
      if( fidx < FunNode.PRIM_CNT ) {
        ret_mem_trimmed = TypeMem.EMPTY_MEM;
        System.out.println("x");
      }
      // Build a full return type.
      TypeTuple tret2 = TypeTuple.make(tret.at(0),ret_mem_trimmed,tret.at(2));
      t = lifting ? t.join(tret2) : t.meet(tret2);

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
  private Node inline( GVNGCM gvn, CallNode call, Node ctl, Node mem, Node rez, RetNode ret ) {
    assert nwired()==0 || nwired()==1; // not wired to several choices

    // Unwire any wired called function
    if( nwired() == 1 && !ret.is_copy() ) {  // Wired, and called function not already collapsing
      FunNode fun = ret.fun();
      for( int i=0; i<fun._defs._len; i++ ) // Unwire
        if( fun.in(i)==ctl ) gvn.set_def_reg(fun,i,gvn.con(Type.XCTRL));
    }
    // Call is also is_copy and will need to collapse
    call._is_copy = true;              // Call is also is-copy
    gvn.add_work(call);
    for( Node use : call._uses ) gvn.add_work(use);
    // Remove all edges except the inlined results
    ctl.keep();  mem.keep();  rez.keep();
    while( _defs._len > 0 ) pop(gvn);
    // Put results back on, and trigger is_copy to collapse
    add_def(ctl.unhook());
    add_def(mem.unhook());
    add_def(rez.unhook());
    return this;
  }
  // If slot 0 is not a CallNode, we have been inlined.
  private boolean is_copy() { return !(in(0) instanceof CallNode); }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return is_copy() ? in(idx) : null; }
  @Override public Type all_type() { return TypeTuple.CALL; }
}
