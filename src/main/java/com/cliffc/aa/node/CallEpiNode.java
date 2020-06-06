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
  public CallEpiNode( Node... nodes ) { super(OP_CALLEPI,nodes);  assert nodes[1] instanceof DefMemNode; }
  String xstr() { return ((is_dead() || is_copy()) ? "x" : "C")+"allEpi"; } // Self short name
  public CallNode call() { return (CallNode)in(0); }
  int nwired() { return _defs._len-2; }
  static int wire_num(int x) { return x+2; }
  RetNode wired(int x) { return (RetNode)in(x+2); }

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

    // See if we can wire any new fidxs directly between Call/Fun and Ret/CallEpi
    if( check_and_wire(gvn) )
      return this;              // Return with progress

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    if( nwired()==1 && fidxs.abit() != -1 ) { // Wired to 1 target
      RetNode ret = wired(0);                 // One wired return
      FunNode fun = ret.fun();
      if( fun != null && fun._defs._len==2 && // Function is only called by 1 (and not the unknown caller)
          call.err(gvn,true)==null &&   // And args are ok
          !fun.noinline() ) {           // And not turned off
        assert fun.in(1).in(0)==call;   // Just called by us
          // TODO: Bring back SESE opts
        fun.set_is_copy(gvn);
        return inline(gvn,level, call, tcall, ret.ctl(), ret.mem(), ret.val(), null/*do not unwire, because using the entire function body inplace*/);
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
      return inline(gvn,level,call,tcall,cctl,cmem,call.arg(((ParmNode)rrez)._idx), ret);
    // Check for constant body
    if( gvn.type(rrez).is_con() && rctl==fun && cmem == rmem)
      return inline(gvn,level,call,tcall,cctl,cmem,rrez,ret);

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
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? call.argm(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = call._badargs;
      return inline(gvn,level,call,tcall,cctl,cmem,gvn.add_work(gvn.xform(irez)),ret); // New exciting replacement for inlined call
    }

    return null;
  }

  // Used during GCP and Ideal calls to see if wiring is possible.
  // Return true if a new edge is wired
  public boolean check_and_wire( GVNGCM gvn ) {
    if( gvn._opt_mode == 0 ) return false; // Graph not formed yet
    if( !(gvn.type(this) instanceof TypeTuple) ) return false; // Collapsing
    CallNode call = call();
    Type tcall = gvn.type(call);
    if( !(tcall instanceof TypeTuple) ) return false;
    BitsFun fidxs = CallNode.ttfp(tcall)._fidxs;
    if( fidxs.above_center() )  return false; // Still choices to be made during GCP.

    // Check all fidxs for being wirable
    boolean progress = false;
    for( int fidx : fidxs ) {                 // For all fidxs
      if( BitsFun.is_parent(fidx) ) continue; // Do not wire parents, as they will eventually settle out
      FunNode fun = FunNode.find_fidx(fidx);  // Lookup, even if not wired
      if( fun.is_forward_ref() ) continue;    // Not forward refs, which at GCP just means a syntax error
      if( _defs.find(fun.ret()) != -1 ) continue; // Wired already
      progress=true;
      wire1(gvn,call,fun,fun.ret()); // Wire Call->Fun, Ret->CallEpi
    }
    return progress;
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds a edges in the graph
  // but NOT in the CG, until _cg_wired gets set.
  void wire1( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
    assert _defs.find(ret)==-1; // No double wiring
    wire0(gvn,call,fun,ret);
    // Wire self to the return
    gvn.add_work(this);
    gvn.add_def(this,ret);
    gvn.add_work(ret);
    gvn.add_work(ret.funptr());
  }

  // Wire without the redundancy check, or adding to the CallEpi
  void wire0( GVNGCM gvn, CallNode call, FunNode fun, RetNode ret ) {
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
      case -2: actual = new MProjNode(call,CallNode.MCEIDX); break;    // Memory into the callee
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
    // tcall[1] = Memory passed around the functions.
    // tcall[2] = Aliases escaping into function
    // tcall[3] = Memory passed into   the functions.
    // tcall[4] = TypeFunPtr passed to FP2Closure
    // tcall[5+]= Arg types
    Type       ctl    = CallNode.tctl(tcall); // Call is reached or not?
    if( ctl != Type.CTRL && ctl != Type.ALL )
      return TypeTuple.CALLE.dual();
    TypeMem    tmem   = CallNode.tmem(tcall); // Peel apart Call tuple
    TypeFunPtr tfptr  = CallNode.ttfp(tcall); // Peel apart Call tuple
    BitsAlias escapes = CallNode.tals(tcall).aliases();

    if( tfptr.is_forward_ref() ) return TypeTuple.CALLE; // Still in the parser.
    // NO fidxs, means we're not calling anything.
    BitsFun fidxs = tfptr.fidxs();
    if( fidxs==BitsFun.EMPTY ) return TypeTuple.CALLE.dual();
    if( fidxs.above_center() ) return TypeTuple.CALLE.dual(); // Not resolved yet
    TypeMem def_mem = (TypeMem)gvn.type(Env.DEFMEM);

    // Any not-wired unknown call targets?
    boolean has_unknown_callees = fidxs==BitsFun.FULL;
    if( !has_unknown_callees ) {
      // If fidxs includes a parent fidx, then it was split - currently exactly
      // in two.  If both children are wired, then proceed to merge both
      // children as expected; same if the parent is still wired (perhaps with
      // some children).  If only 1 child is wired, then we have an extra fidx
      // for a not-wired child.  If this fidx is really some unknown caller we
      // would have to get super conservative; but its actually just a recently
      // split child fidx.  If we get the fidx via FunNode.find_fidx we suffer
      // the non-local progress curse.  If we get super conservative, we end up
      // rolling backwards (original fidx returned int; each split will only
      // ever return int-or-better).  So instead we "freeze in place".
      BitsFun ws = BitsFun.EMPTY;
      for( int i=0; i<nwired(); i++ )
        ws = ws.set(wired(i)._fidx);
      for( int fidx : fidxs ) {
        boolean fwired=false;
        int kids=0;
        for( int i=0; i<nwired(); i++ ) {
          int rfidx = wired(i)._fidx;
          if( fidx == rfidx ) { fwired=true; break; } // Directly wired is always OK
          if( fidx == BitsFun.parent(rfidx) ) kids++; // Both kids of a split parent is OK.
        }
        if( !fwired ) {         // Directly wired is always OK
          if( BitsFun.is_parent(fidx) ) { // Child of a split parent, need both kids wired
            if( kids!=2 ) return gvn.self_type(this); // "Freeze in place"
          } else
            has_unknown_callees = gvn._opt_mode<2; // Assume unknown callers (or not) according to starting assumptions
        }
      }
    }

    // Compute call-return value from all callees
    Type tret = Type.ALL;       // Unknown caller returns a type error
    if( !has_unknown_callees ) {
      tret = Type.ANY;
      for( int i=0; i<nwired(); i++ )
        if( fidxs.test_recur(wired(i)._fidx) )
          tret = tret.meet(((TypeTuple)gvn.type(wired(i))).at(2));
    }

    // For every alias
    //   if it does not escape, use caller (not callee) memory.
    //     Unless caller is XOBJ, and callee is legit; then assume its a New allocation
    //   if it DOES     escape
    //     If any FIDX has no ret, use DEFMEM (assume unwired call is bad)
    //     Else FIDX has Ret, merge all such Rets.
    //     Ignore Rets with no FIDX.
    int emax = Math.max(Math.max(escapes.max()+1,def_mem.len()),tmem.len());
    TypeObj[] tos = new TypeObj[emax];
    tos[1] = def_mem.at(1);
    for( int alias=2; alias<emax; alias++ ) {
      TypeObj rhs = TypeObj.OBJ; // Unknown caller modifies all memory
      if( !has_unknown_callees ) {
        rhs = TypeObj.UNUSED;
        for( int i=0; i<nwired(); i++ )
          if( fidxs.test_recur(wired(i)._fidx) ) {
            RetNode ret = wired(i);
            TypeTuple ttret = (TypeTuple)gvn.type(ret);
            TypeMem trmem = (TypeMem)ttret.at(1);
            TypeObj tro = trmem.at(alias);
            rhs = (TypeObj)rhs.meet(tro);
          }
      }
      TypeObj to = gvn._opt_mode==2 ? rhs : tmem.merge_one_lhs(escapes,alias,rhs);  // always escape in GCP
      tos[alias] = (TypeObj)to.join(def_mem.at(alias));// But always at least as nice as DEFMEM
    }
    TypeMem post_call_mem = TypeMem.make0(tos);
    // Final result
    TypeTuple rez = TypeTuple.make(Type.CTRL,post_call_mem,tret);
    return rez;
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
  private Node inline( GVNGCM gvn, int level, CallNode call, TypeTuple tcall, Node ctl, Node mem, Node rez, RetNode ret ) {
    assert (level&1)==0; // Do not actually inline, if just checking that all forward progress was found
    assert nwired()==0 || nwired()==1; // not wired to several choices

    Node precallmem = call.mem();
    if( precallmem!=mem ) {
      // Split call memory, same as CallNode does
      BitsAlias escapes = CallNode.tals(tcall)._aliases;
      if( escapes!=BitsAlias.NZERO ) { // All escape: no need to split/rejoin
        Node split = gvn.xform(new MemSplitNode(precallmem,escapes,call._live).keep());
        Node lhs = gvn.xform(new MProjNode(split,0)); lhs._live = call._live; // Caller memory (bypass)
        Node rhs = gvn.xform(new MProjNode(split,1)); rhs._live = call._live; // Callee memory (escapes into call)
        // Memory into the call comes from the split.  Call will disappear shortly.
        gvn.set_def_reg(call,1,rhs);
        // Merge the call-split and pre-call memory.
        mem = gvn.xform(new MemJoinNode(lhs,mem,Env.DEFMEM,escapes,_live));
        split.unkeep(gvn);
      }
    }

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
