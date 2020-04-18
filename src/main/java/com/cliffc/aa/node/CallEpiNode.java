package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

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

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;

    CallNode call = call();
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    if( tcall.at(0) != Type.CTRL ) return null; // Call not executable
    // Get calls resolved function.
    if( !(tcall.at(2) instanceof TypeFunPtr) ) return null; // No known function pointer
    TypeFunPtr tfp = (TypeFunPtr)tcall.at(2);

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    BitsFun fidxs = tfp.fidxs();
    if( nwired()==1 && fidxs.abit() != -1 ) { // Wired to 1 target
      RetNode ret = wired(0);                 // One wired return
      FunNode fun = ret.fun();
      if( fun != null && fun._defs._len==2 && // Function is only called by 1 (and not the unknown caller)
          call.err(gvn,true)==null ) {  // And args are ok
        assert fun.in(1).in(0)==call;   // Just called by us
          // TODO: Bring back SESE opts
        fun.set_is_copy(gvn);
        return inline(gvn,level, call, ret.ctl(), ret.mem(), ret.val(), null/*do not unwire, because using the entire function body inplace*/);
      }
    }

    // If the call's allowed functions excludes any wired, remove the extras
    if( !fidxs.test(BitsFun.ALL) ) {
      for( int i = 0; i < nwired(); i++ ) {
        RetNode ret = wired(i);
        if( !fidxs.test_recur(ret.fidx()) ) { // Wired call not in execution set?
          assert !BitsFun.is_parent(ret.fidx());
          // Remove the edge.  Pre-GCP all CG edges are virtual, and are lazily
          // and pessimistically filled in by ideal calls.  During the course
          // of lifting types some of the manifested CG edges are killed.
          // Post-GCP all CG edges are manifest, but types can keep lifting
          // and so CG edges can still be killed.
          unwire(gvn,call,ret);
          del(wire_num(i));
          return this; // Return with progress
        }
      }
    }

    // Only inline wired single-target function with valid args.  CallNode wires.
    if( nwired()!=1 ) return null;
    int fidx = fidxs.abit();      // Could be 1 or multi
    if( fidx == -1 ) return null; // Multi choices, only 1 wired at the moment.
    //assert !fidxs.above_center(); // Since wired, not above center
    if( fidxs.above_center() )
      return null;

    if( call.err(gvn,true)!=null ) return null; // CallNode claims args in-error, do not inline

    // Call allows 1 function not yet wired, sanity check it.
    int cnargs = call.nargs();
    FunNode fun = FunNode.find_fidx(fidx);
    assert !fun.is_forward_ref() && !fun.is_dead()
      && gvn.type(fun) == Type.CTRL
      && fun.nargs() == cnargs; // All checked by call.err
    RetNode ret = fun.ret();    // Return from function
    assert ret!=null;

    // Single choice; check compatible args and no conversions needed.
    TypeStruct formals = fun._tf._args;
    for( Node parm : fun._uses ) {
      if( parm instanceof ParmNode && parm.in(0)==fun ) {
        int idx = ((ParmNode)parm)._idx;
        if( idx == -1 ) continue; // RPC not an arg
        Node arg = idx==-2 ? call.mem() : call.arg(idx);
        Type actual = gvn.type(arg);
        // Display arg comes from function pointer
        if( idx==0 ) actual = (actual instanceof TypeFunPtr) ? ((TypeFunPtr)actual).display() : Type.SCALAR;
        Type tparm = gvn.type(parm); // Pre-GCP this should be the default type
        if( !actual.isa(tparm) ||  // Not compatible
            (idx >= 0 && actual.isBitShape(formals.at(idx)) == 99) ) { // Requires user-specified conversion
          return null;
        }
      }
    }


    // Check for several trivial cases that can be fully inlined immediately.
    Node cctl = call.ctl();
    Node cmem = call.mem();
    Node rctl = ret.ctl();      // Control being returned
    Node rmem = ret.mem();      // Memory  being returned
    Node rrez = ret.val();      // Value   being returned
    // If the function does nothing with memory, then use the call memory directly.
    if( (rmem instanceof ParmNode && rmem.in(0) == fun) || gvn.type(rmem)==TypeMem.XMEM )
      rmem = cmem;

    // Check for zero-op body (id function)
    if( rrez instanceof ParmNode && rrez.in(0) == fun && cmem == rmem )
      return inline(gvn,level,call,cctl,cmem,call.arg(((ParmNode)rrez)._idx), ret);
    // Check for constant body
    if( gvn.type(rrez).is_con() && rctl==fun && cmem == rmem)
      return inline(gvn,level,call,cctl,cmem,rrez,ret);

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
      irez._live = _live; // Keep liveness from CallEpi, as the original might be dead.
      for( Node parm : rrez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? call.arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = call._badargs;
      return inline(gvn,level,call,cctl,cmem,gvn.add_work(gvn.xform(irez)),ret); // New exciting replacement for inlined call
    }

    return null;
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds an edge in the Call-Graph.
  boolean wire( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
    assert _keep==0;            // not expecting this during calls

    for( int i=0; i<nwired(); i++ )
      if( wired(i) == ret )     // Look for same Ret
        return false;           // Already wired up

    wire0(gvn,call,fun);
    gvn.add_def(this,ret);
    gvn.add_work(ret);
    gvn.add_work(ret.funptr());
    return true;
  }

  // Wire without the redundancy check, or adding to the CallEpi
  void wire0( GVNGCM gvn, CallNode call, FunNode fun ) {
    // Wire.  During GCP, cannot call "xform" since e.g. types are not final
    // nor constant yet - and need to add all new nodes to the GCP worklist.
    // During iter(), must call xform() to register all new nodes.

    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) != fun || !(arg instanceof ParmNode) ) continue;
      // See CallNode output tuple type for what these horrible magic numbers are.
      Node actual;
      int idx = ((ParmNode)arg)._idx;
      switch( idx ) {
      case  1: actual = new FP2ClosureNode(call); break; // Filter Function Pointer to Closure
      case -1: actual = new ConNode<>(TypeRPC.make(call._rpc)); break; // Always RPC is a constant
      case -2: actual = new MProjNode(call,1); break;    // Memory
      default: actual = idx >= call.nargs()              // Check for args present
          ? new ConNode<>(Type.XSCALAR) // Missing args, still wire (to keep FunNode neighbors) but will error out later.
          : new ProjNode(call,idx+1);   // Normal args
        break;
      }
      actual = gvn._opt_mode == 2 ? gvn.new_gcp(actual) : gvn.xform(actual);
      gvn.add_def(arg,actual);
    }

    // Add matching control to function via a CallGraph edge.
    Node callgrf = new CProjNode(call,0);
    callgrf = gvn._opt_mode == 2 ? gvn.new_gcp(callgrf) : gvn.xform(callgrf);
    gvn.add_def(fun,callgrf);
  }

  // Merge call-graph edges, but the call-graph is not discovered prior to GCP.
  // If the Call's type includes all-functions, then the CallEpi must assume
  // unwired Returns may yet appear, and be conservative.  Otherwise it can
  // just meet the set of known functions.
  @Override public TypeTuple value(GVNGCM gvn) {

    if( is_copy() )
      return gvn.type(in(0))!=Type.CTRL
        ? TypeTuple.CALLE.dual()
        : TypeTuple.make(gvn.type(in(0)),gvn.type(in(1)),gvn.type(in(2)));
    // Get Call result.  If the Call args are in-error, then the Call is called
    // and we flow types to the post-call.... BUT the bad args are NOT passed
    // along to the function being called.
    // tcall[0] = Control
    // tcall[1] = Memory passed into the functions.
    // tcall[2] = TypeFunPtr passed to FP2Closure
    // tcall[3+]= Arg types
    CallNode call = call();
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    Type ctl = tcall.at(0); // Call is reached or not?
    if( ctl != Type.CTRL && ctl != Type.ALL )
      return TypeTuple.CALLE.dual();

    Type tfptr = tcall.at(2);
    if( !(tfptr instanceof TypeFunPtr) ) // Call does not know what it is calling?
      return TypeTuple.CALLE;

    // If pre-gcp, we may have unknown callers.  Be very conservative until we
    // have wired all callers.
    BitsFun fidxs = ((TypeFunPtr)tfptr).fidxs();
    if( gvn._opt_mode < 2 && fidxs.bitCount() > nwired() )
      return TypeTuple.CALLE;
    // NO fidxs, means we're not calling anything.
    if( fidxs==BitsFun.EMPTY ) return TypeTuple.CALLE.dual();
    if( fidxs.above_center() ) return TypeTuple.CALLE.dual();
    // Meet across wired callers.
    TypeTuple tt = TypeTuple.XRET;
    for( int i=0; i<nwired(); i++ ) {
      Node ret = in(wire_num(i));
      if( ret instanceof RetNode &&            // Only fails during testing
          ((RetNode)ret).is_copy() ) continue; // Dying, not called, not returning here
      Type tr = gvn.type(ret);
      if( !(tr instanceof TypeTuple) || // Only fails during testing
          ((TypeTuple)tr)._ts.length != TypeTuple.XRET._ts.length )
        continue;               // Only fails during testing
      tt = (TypeTuple)tt.meet(tr);
    }
    return tt;
  }

  // Inline the CallNode.  Remove all edges except the results.  This triggers
  // "is_copy()", which in turn will trigger the following ProjNodes to inline.
  private Node inline( GVNGCM gvn, int level, CallNode call, Node ctl, Node mem, Node rez, RetNode ret ) {
    assert (level&1)==0; // Do not actually inline, if just checking that all forward progress was found
    assert nwired()==0 || nwired()==1; // not wired to several choices

    // Unwire any wired called function
    if( ret != null && nwired() == 1 && !ret.is_copy() ) // Wired, and called function not already collapsing
      unwire(gvn,call,ret);
    // Call is also is_copy and will need to collapse
    call._is_copy = true;              // Call is also is-copy
    gvn.add_work_uses(call.keep());
    // Remove all edges except the inlined results
    ctl.keep();  mem.keep();  rez.keep();
    while( _defs._len > 0 ) pop(gvn);
    // Put results back on, and trigger is_copy to collapse
    add_def(ctl .unhook());
    add_def(mem .unhook());
    add_def(rez .unhook());
    add_def(call.unhook());     // Hook call, to get FIDX for value filtering.
    return this;
  }

  void unwire(GVNGCM gvn, CallNode call, RetNode ret) {
    if( ret.is_copy() ) return;
    FunNode fun = ret.fun();
    for( int i=1; i<fun._defs._len; i++ ) // Unwire
      if( fun.in(i).in(0)==call ) gvn.set_def_reg(fun,i,gvn.con(Type.XCTRL));
    gvn.add_work_uses(fun);
  }

  // Compute local contribution of use liveness to this def.  If the call is
  // Unresolved, then none of CallEpi targets are (yet) alive.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    assert _keep==0;
    // If is_copy, then basically acting like pass-thru.
    if( !is_copy() && def != call() ) { // Not a copy, check call site
      // The given function is alive, only if the Call will Call it.
      TypeTuple tcall = (TypeTuple)gvn.type(call());
      BitsFun fidxs = ((TypeFunPtr)tcall.at(2)).fidxs();
      int fidx = ((RetNode)def).fidx();
      if( fidxs.above_center() || !fidxs.test(fidx) )
        return TypeMem.DEAD;    // Call does not call this, so not alive.
      // Target is as alive as we are.
      return _live;
    }
    // Call is as alive as we are, demanding what we demand.  Since Call is
    // alive, the FunPtr to the Call is also alive, even if the targets are not
    // alive (because the FunPtr has XSCALAR value).
    if( _live==TypeMem.DEAD ) return TypeMem.DEAD;
    return _live.at(1) == TypeObj.OBJ ? TypeMem.make(1,TypeObj.OBJ) : TypeMem.EMPTY;
  }
  @Override public boolean basic_liveness() { return false; }

  // If slot 0 is not a CallNode, we have been inlined.
  boolean is_copy() { return !(in(0) instanceof CallNode); }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return is_copy() ? in(idx) : null; }
  @Override public Type all_type() { return TypeTuple.CALLE; }
}
