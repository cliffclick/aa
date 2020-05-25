package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// See CallNode.  Slot 0 is the Call.  The remaining slots are Returns which
// are typed as standard function returns: {Ctrl,Mem,Val}.  These Returns
// represent call-graph edges that are known to be possible and thus their fidx
// appears in the Call's BitsFun type.
//
// Pre-opto it is possible for the all-functions type to appear at a Call, and
// in this case the CallEpi must assume all possible calls may happen, they are
// just not wired up yet.
//
// It is also possible that we have discovered and wired up a function, but
// that the input/output types are not yet monotonic, and we do not flow values
// across those edges until the types align.  This is controlled with a small
// bit-vector.

public final class CallEpiNode extends Node {
  public CallEpiNode( Node... nodes ) { super(OP_CALLEPI,nodes);  assert nodes[1] instanceof DefMemNode; _cg_wired = BitsFun.EMPTY; }
  String xstr() { return ((is_dead() || is_copy()) ? "x" : "C")+"allEpi"; } // Self short name
  public CallNode call() { return (CallNode)in(0); }
  int nwired() { return _defs._len-2; }
  static int wire_num(int x) { return x+2; }
  RetNode wired(int x) { return (RetNode)in(x+2); }

  // Set of FIDXS that are both wired & flowing types.
  BitsFun _cg_wired;

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;

    CallNode call = call();
    Type tc = gvn.type(call);
    if( !(tc instanceof TypeTuple) ) return null;
    TypeTuple tcall = (TypeTuple)tc;
    if( CallNode.tctl(tcall) != Type.CTRL ) return null; // Call not executable
    // Get calls resolved function.
    BitsFun fidxs = CallNode.ttfp(tcall).fidxs();

    // If the call's allowed functions excludes any wired, remove the extras
    if( !fidxs.test(BitsFun.ALL) ) { // Shortcut
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
          return this; // Return with progress
        }
      }
    }

    // See if we can flow more wired CG edges.
    if( _cg_wired != fidxs ) {
      //TODO: Surely must be in value() so GCP wires
      TypeMem callmem = CallNode.tmem(tcall);
      Type tci = gvn.type(this);
      if( !(tci instanceof TypeTuple ) ) return null;
      TypeMem cepimem = (TypeMem)((TypeTuple)tci)._ts[1];
      BitsFun progress = _cg_wired;
      for( int fidx : fidxs ) {                 // For all fidxs
        if( BitsFun.is_parent(fidx) ) continue; // Do not wire parents, as they will eventually settle out
        FunNode fun = FunNode.find_fidx(fidx);  // Lookup, even if not wired
        if( fun.is_forward_ref() ) continue;    // Not forward refs, which at GCP just means a syntax error
        if( cg_tst(fidx) ) continue;            // Already wired
        if( _defs.find(fun.ret()) == -1 ) continue; // Wire before flow-enable
        // Wiring a Call brings in memory that the Call knows into what the
        // Function knows.  These can be out-of-sync, if one or the other has
        // propagated knowledge of e.g. new allocations.  Stall wiring until
        // the types are properly "isa".
        ParmNode fmem = fun.parm(-2);
        if( fmem != null ) {
          Type funmem = gvn.type(fmem);
          if( !callmem.isa(funmem) ) // If call is lower than Parm:mem, the Parm will drop - not allowed
            continue;
        }
        // Same for the reverse path from Return to CallEpi; the CallEpi must
        // merge all returns and also is conservative, so it must remain
        // at or below the returns, but only along the escaped aliases.
        RetNode ret = fun.ret();
        TypeMem retmem = (TypeMem)((TypeTuple)gvn.type(ret ))._ts[1];
        if( !retmem.isa_escape(cepimem,CallNode.tals(tcall).aliases()) )
          continue;
        cg_set(fidx);           // Set bit, wired and flowing types
      }
      if( _cg_wired != progress ) return this;
    }

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    if( nwired()==1 && fidxs.abit() != -1 && fidxs.isa(_cg_wired) ) { // Wired to 1 target
      RetNode ret = wired(0);                 // One wired return
      FunNode fun = ret.fun();
      if( fun != null && fun._defs._len==2 && // Function is only called by 1 (and not the unknown caller)
          call.err(gvn,true)==null &&   // And args are ok
          !fun.noinline() ) {           // And not turned off
        assert fun.in(1).in(0)==call;   // Just called by us
          // TODO: Bring back SESE opts
        fun.set_is_copy(gvn);
        return inline(gvn,level, call, ret.ctl(), ret.mem(), ret.val(), null/*do not unwire, because using the entire function body inplace*/);
      }
    }

    // Only inline wired single-target function with valid args.  CallNode wires.
    if( nwired()!=1 ) return null; // More than 1 wired, inline only via FunNode
    int fidx = fidxs.abit();       // Could be 1 or multi
    if( fidx == -1 ) return null;  // Multi choices, only 1 wired at the moment.
    if( fidxs.above_center() )     // Can be unresolved yet
      return null;

    if( call.err(gvn,true)!=null ) return null; // CallNode claims args in-error, do not inline

    // Call allows 1 function not yet inlined, sanity check it.
    int cnargs = call.nargs();
    FunNode fun = FunNode.find_fidx(fidx);
    assert !fun.is_forward_ref() && !fun.is_dead()
      && gvn.type(fun) == Type.CTRL
      && fun.nargs() == cnargs; // All checked by call.err
    RetNode ret = fun.ret();    // Return from function
    assert ret!=null;

    // Single choice; check compatible args and no conversions needed.
    TypeStruct formals = fun._sig._formals;
    for( Node parm : fun._uses ) {
      if( parm instanceof ParmNode && parm.in(0)==fun ) {
        int idx = ((ParmNode)parm)._idx;
        if( idx == -1 ) continue; // RPC not an arg
        Node arg = idx==-2 ? call.mem() : call.arg(idx);
        Type actual = gvn.type(arg);
        // Display arg comes from function pointer
        if( idx==0 ) actual = (actual instanceof TypeFunPtr) ? ((TypeFunPtr)actual)._disp : Type.SCALAR;
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
    // Check that function return memory and post-call memory are compatible
    TypeTuple tself = (TypeTuple)gvn.type(this);
    if( !gvn.type(rmem).isa( tself.at(1)) )
      return null;

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
      Node irez = rrez.copy(false,gvn);// Copy the entire function body
      irez._live = _live; // Keep liveness from CallEpi, as the original might be dead.
      for( Node parm : rrez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? call.arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = call._badargs;
      return inline(gvn,level,call,cctl,cmem,gvn.add_work(gvn.xform(irez)),ret); // New exciting replacement for inlined call
    }

    return null;
  }

  boolean cg_tst(int fidx) { return _cg_wired.test_recur(fidx); }

  // Used during code-cloning to remove the parent fidx, and add one or more children.
  void cg_clr(int fidx) {
    assert cg_tst(fidx);
    _cg_wired = _cg_wired.clear(fidx);
  }
  void cg_set(int fidx) { _cg_wired = _cg_wired.set(fidx); }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds a edges in the graph
  // but NOT in the CG, until _cg_wired gets set.
  boolean wire( GVNGCM gvn, CallNode call, FunNode fun ) {
    assert _keep==0;            // not expecting this during calls
    RetNode ret = fun.ret();
    for( int i=0; i<nwired(); i++ )
      if( wired(i) == ret )     // Look for same Ret
        return false;           // Already wired up
    wire1(gvn,call,fun,ret);
    return true;
  }

  // Wire, adding self AND setting the CG edge.  Used by FunNode
  // cloning, which guarantees types are correct beforehand.
  void wire2( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
    wire1(gvn,call,fun,ret);
    cg_set(fun._fidx);
  }

  // Wire, then add self to the return
  void wire1( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
    wire0(gvn,call,fun);
    // Wire self to the return
    gvn.add_def(this,ret);
    gvn.add_work(ret);
    gvn.add_work(ret.funptr());
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
      case  0: actual = new FP2ClosureNode(call); break; // Filter Function Pointer to Closure
      case -1: actual = new ConNode<>(TypeRPC.make(call._rpc)); break; // Always RPC is a constant
      case -2: actual = new MProjNode(call,CallNode.MEMIDX); break;    // Memory into the callee
      default: actual = idx >= call.nargs()              // Check for args present
          ? new ConNode<>(Type.XSCALAR) // Missing args, still wire (to keep FunNode neighbors) but will error out later.
          : new ProjNode(call,idx+CallNode.ARGIDX); // Normal args
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
  @Override public Type value(GVNGCM gvn) {
    Node call = in(0);
    Type tin0 = gvn.type(call);  TypeTuple tcall;
    // Check for is_copy, based on types: if input is NOT a call-type then we
    // are an inlined XallEpi and make a call-like tuple directly from our
    // inputs.
    if( !(tin0 instanceof TypeTuple) ||
        (tcall=(TypeTuple)tin0)._ts.length <= CallNode.ARGIDX ) { // Must be inlined
      if( tin0!=Type.CTRL ) return tin0.oob();     // Weird stuff?
      // Must be an is_copy.  Just return the arg types.
      return TypeTuple.make(Type.CTRL,gvn.type(in(1)),gvn.type(in(2)));
    }
    //assert sane_wiring();

    // Get Call result.  If the Call args are in-error, then the Call is called
    // and we flow types to the post-call.... BUT the bad args are NOT passed
    // along to the function being called.
    // tcall[0] = Control
    // tcall[1] = Memory passed into the functions.
    // tcall[2] = TypeFunPtr passed to FP2Closure
    // tcall[3+]= Arg types
    Type ctl = CallNode.tctl(tcall); // Call is reached or not?
    if( ctl != Type.CTRL && ctl != Type.ALL )
      return TypeTuple.CALLE.dual();

    TypeMem tmem = CallNode.tmem(tcall);
    TypeFunPtr tfptr = CallNode.ttfp(tcall);

    BitsFun fidxs = tfptr.fidxs();
    if( tfptr.is_forward_ref() ) return TypeTuple.CALLE; // Still in the parser.
    // NO fidxs, means we're not calling anything.
    if( fidxs==BitsFun.EMPTY ) return TypeTuple.CALLE.dual();
    if( fidxs.above_center() ) return TypeTuple.CALLE.dual(); // Not resolved yet

    // If call memory is not at least default memory - stall typing until the
    // Call catches up.  Might need to bring default memory into a Call.
    TypeMem post_call_mem = (TypeMem)gvn.type(Env.DEFMEM);
    if( !tmem.isa(post_call_mem) ) {
      // Self type, except easier to report a sane lower bound.
      Type self = gvn.self_type(this);
      return self==null || self==Type.ALL ? TypeTuple.CALLE : self;
    }

    // Take Call reach-around aliases, and stomp/merge-over from pre-call
    // memory.  These never made it into the function, and were not modified
    // (or even visible).
    BitsAlias escapes = CallNode.tals(tcall).aliases();
    int emax = Math.max(Math.max(escapes.max()+1,post_call_mem.len()),tmem.len());
    for( int escape=2; escape<emax; escape++ ) {
      if( !escapes.test_recur(escape) ) { // A non-escaping alias
        TypeObj tesc = tmem.at(escape);// The pre-call value
        if( post_call_mem.at(escape) != tesc &&
            (tesc!=TypeObj.XOBJ && tesc !=TypeObj.UNUSED) ) // And pre-call HAS a value, other might be made IN the function & escaping out
          post_call_mem = post_call_mem.set(escape,tesc);
      }
    }

    // Crush all the non-finals across the call
    TypeTuple post_call_crush = TypeTuple.make(Type.CTRL,post_call_mem,Type.ALL);
    TypeTuple mt = post_call_crush;

    // Are all call targets known, wired & enabled?
    // Then can lift to the meet-across of returns.
    if( fidxs.isa(_cg_wired) ) {
      TypeTuple tret = TypeTuple.XRET;    // Start high and 'meet'
      for( int i=0; i<nwired(); i++ ) {
        Node ret = in(wire_num(i));
        if( ret instanceof RetNode &&            // Only fails during testing
            ((RetNode)ret).is_copy() ) continue; // Dying, not called, not returning here
        Type tr = gvn.type(ret);          // Allow ConNode here for testing
        if( !(tr instanceof TypeTuple) || // Only fails during testing
            ((TypeTuple)tr)._ts.length != TypeTuple.XRET._ts.length )
          continue;               // Only fails during testing
        if( !fidxs.test_recur(((RetNode)ret)._fidx) ) continue; // Wired, but fptr does not reach here
        tret = (TypeTuple)tret.meet(tr);
      }
      // Still must join with the post_call_crush, because the return knows as
      // much as the crushed-call does in all cases.  Needed with recursive
      // calls pre-GCP, as the tail-call-loop can never lift on its own.
      mt = (TypeTuple)tret.join(post_call_crush);
    }

    return mt;
  }

  // Does this set of aliases bypass the call?
  CallNode can_bypass( GVNGCM gvn, BitsAlias aliases ) {
    if( !(in(0) instanceof CallNode) ) return null;
    CallNode call = call();
    Type tcall = gvn.type(call);
    if( tcall == Type.ANY ) return null;
    TypeMemPtr tmp = CallNode.tals(tcall);
    if( tmp._aliases.join(aliases) != BitsAlias.EMPTY ) return null;
    Type tret = ((TypeTuple)gvn.type(this))._ts[2];
    if( TypeMemPtr.OOP.isa(tret) ) return null; // Might return an aliased pointer
    if( tret instanceof TypeMemPtr )
      if( ((TypeMemPtr)tret)._aliases.join(aliases) != BitsAlias.EMPTY ) return null;
    // Load/Store can bypass this call.
    return call;
  }

  // Sanity check
  boolean sane_wiring() {
    CallNode call = call();
    ProjNode cprj = ProjNode.proj(call,0); // Control proj
    if( cprj==null ) return true; // Abort check, call is dead
    for( int i=0; i<nwired(); i++ ) {
      RetNode ret = wired(i);
      if( ret.is_copy() ) return true; // Abort check, will be misaligned until dead path removed
      FunNode fun = ret.fun();
      if( cprj._uses.find(fun) == -1 )
        return false;           // ith usage is ith wire
    }
    return true;
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
    assert sane_wiring();
    if( !ret.is_copy() ) {
      FunNode fun = ret.fun();
      for( int i = 1; i < fun._defs._len; i++ ) // Unwire
        if( fun.in(i).in(0) == call ) {
          gvn.set_def_reg(fun, i, gvn.con(Type.XCTRL));
          break;
        }
      gvn.add_work_uses(fun);
    }
    del(_defs.find(ret));
    assert sane_wiring();
  }

  // Compute local contribution of use liveness to this def.  If the call is
  // Unresolved, then none of CallEpi targets are (yet) alive.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    assert _keep==0;
    if( def instanceof DefMemNode ) return _live;
    // If is_copy, then basically acting like pass-thru.
    if( !is_copy() && def != call() ) { // Not a copy, check call site
      // The given function is alive, only if the Call will Call it.
      Type tcall = gvn.type(call());
      if( !(tcall instanceof TypeTuple) ) return tcall.above_center() ? TypeMem.DEAD : _live;
      BitsFun fidxs = CallNode.ttfp(tcall).fidxs();
      int fidx = ((RetNode)def).fidx();
      if( fidxs.above_center() || !fidxs.test(fidx) )
        return TypeMem.DEAD;    // Call does not call this, so not alive.
    }
    // Target is as alive as we are.
    return _live;
  }
  @Override public boolean basic_liveness() { return false; }

  // If slot 0 is not a CallNode, we have been inlined.
  boolean is_copy() { return !(in(0) instanceof CallNode); }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return is_copy() ? in(idx) : null; }
  @Override Node is_pure_call() { return call().is_pure_call(); }
}
