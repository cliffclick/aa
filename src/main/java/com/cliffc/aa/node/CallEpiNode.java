package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

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
  String xstr() { return (is_dead() ? "X" : "C")+"allEpi";  } // Self short name
  public CallNode call() { return (CallNode)in(0); }
  @Override public boolean is_mem() { return true; }
  int nwired() { return _defs._len-2; }
  RetNode wired(int x) { return (RetNode)in(x+2); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    CallNode call = call();
    Type tc = call.val();
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
      Type tdef = Env.DEFMEM.val();
      TypeTuple tret = ret.val() instanceof TypeTuple ? (TypeTuple) ret.val() : (TypeTuple) ret.val().oob(TypeTuple.RET);
      Type tretmem = tret.at(1);
      if( fun != null && fun._defs._len==2 && // Function is only called by 1 (and not the unknown caller)
          call.err(true)==null &&       // And args are ok
          CallNode.emem(tcall).isa(tdef) &&
          tretmem.isa(tdef) &&          // Call and return memory at least as good as default
          call.mem().in(0) != call &&   // Dead self-recursive
          fun.in(1)._uses._len==1 &&    // And only calling fun
          ret._live.isa(_live) &&       // Call and return liveness compatible
          !fun.noinline() ) {           // And not turned off
        assert fun.in(1).in(0)==call;   // Just called by us
        fun.set_is_copy(gvn);
        return inline(gvn,level, call, ret.ctl(), ret.mem(), ret.rez(), null/*do not unwire, because using the entire function body inplace*/,call._uid);
      }
    }

    // Parser thunks eagerly inline
    if( call.fun() instanceof ThretNode ) {
      ThretNode tret = (ThretNode)call.fun();
      wire1(gvn,call,tret.thunk(),tret);
      return inline(gvn,level, call, tret.ctrl(), tret.mem(), tret.rez(), null/*do not unwire, because using the entire function body inplace*/,call._uid);
    }

    // Only inline wired single-target function with valid args.  CallNode wires.
    if( nwired()!=1 ) return null; // More than 1 wired, inline only via FunNode
    int fidx = fidxs.abit();       // Could be 1 or multi
    if( fidx == -1 ) return null;  // Multi choices, only 1 wired at the moment.
    if( fidxs.above_center() ) return null; // Can be unresolved yet
    if( BitsFun.is_parent(fidx) ) return null; // Parent, only 1 child wired

    if( call.err(true)!=null ) return null; // CallNode claims args in-error, do not inline

    // Call allows 1 function not yet inlined, sanity check it.
    int cnargs = call.nargs();
    FunNode fun = FunNode.find_fidx(fidx);
    assert !fun.is_forward_ref() && !fun.is_dead()
      && fun.val() == Type.CTRL
      && fun.nargs() == cnargs; // All checked by call.err
    RetNode ret = fun.ret();    // Return from function
    if( ret==null ) return null;

    // Single choice; check no conversions needed.
    TypeTuple formals = fun._sig._formals;
    for( Node parm : fun._uses ) {
      if( parm instanceof ParmNode && parm.in(0)==fun ) {
        int idx = ((ParmNode)parm)._idx;
        if( idx < 0 ) continue; // RPC, Mem
        Type actual = CallNode.targ(tcall,idx);
        // Display arg comes from function pointer
        if( idx==0 ) actual = (actual instanceof TypeFunPtr) ? ((TypeFunPtr)actual)._disp : Type.SCALAR;
        if( actual.isBitShape(formals.at(idx)) == 99 ) // Requires user-specified conversion
          return null;
      }
    }


    // Check for several trivial cases that can be fully inlined immediately.
    Node cctl = call.ctl();
    Node cmem = call.mem();
    Node rctl = ret.ctl();      // Control being returned
    Node rmem = ret.mem();      // Memory  being returned
    Node rrez = ret.rez();      // Result  being returned
    boolean inline = !fun.noinline();
    // If the function does nothing with memory, then use the call memory directly.
    if( (rmem instanceof ParmNode && rmem.in(0) == fun) || rmem.val() ==TypeMem.XMEM )
      rmem = cmem;
    // Check that function return memory and post-call memory are compatible
    if( !(val() instanceof TypeTuple) ) return null;
    Type selfmem = ((TypeTuple) val()).at(1);
    if( !rmem.val().isa( selfmem ) && !(selfmem==TypeMem.ANYMEM && call.is_pure_call()!=null) )
      return null;

    // Check for zero-op body (id function)
    if( rrez instanceof ParmNode && rrez.in(0) == fun && cmem == rmem && inline )
      return inline(gvn,level,call, cctl,cmem,call.arg(((ParmNode)rrez)._idx), ret,call._uid);
    // Check for constant body
    Type trez = rrez.val();
    if( trez.is_con() && rctl==fun && cmem == rmem && inline )
      return inline(gvn,level,call, cctl,cmem,gvn.con(trez),ret,call._uid);

    // Check for a 1-op body using only constants or parameters and no memory effects
    boolean can_inline=!(rrez instanceof ParmNode) && rmem==cmem && inline;
    for( Node parm : rrez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rrez.copy(false,gvn);// Copy the entire function body
      irez._in=false;
      ProjNode proj = ProjNode.proj(this,2);
      irez._live = proj==null ? TypeMem.ESCAPE : proj._live;
      for( Node parm : rrez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? call.argm(((ParmNode)parm)._idx,gvn) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = call._badargs;
      return inline(gvn,level,call, cctl,cmem,gvn.add_work(gvn.xform(irez)),ret,call._uid); // New exciting replacement for inlined call
    }

    return null;
  }

  // Used during GCP and Ideal calls to see if wiring is possible.
  // Return true if a new edge is wired
  public boolean check_and_wire( GVNGCM gvn ) {
    if( !(val() instanceof TypeTuple) ) return false; // Collapsing
    CallNode call = call();
    Type tcall = call.val();
    if( !(tcall instanceof TypeTuple) ) return false;
    BitsFun fidxs = CallNode.ttfp(tcall)._fidxs;
    if( fidxs.above_center() )  return false; // Still choices to be made during GCP.

    // Check all fidxs for being wirable
    boolean progress = false;
    for( int fidx : fidxs ) {                 // For all fidxs
      if( BitsFun.is_parent(fidx) ) continue; // Do not wire parents, as they will eventually settle out
      FunNode fun = FunNode.find_fidx(fidx);  // Lookup, even if not wired
      if( fun.is_dead() ) continue;           // Already dead, stale fidx
      if( fun.is_forward_ref() ) continue;    // Not forward refs, which at GCP just means a syntax error
      RetNode ret = fun.ret();
      if( ret==null ) continue;               // Mid-death
      if( _defs.find(ret) != -1 ) continue;   // Wired already
      progress=true;
      wire1(gvn,call,fun,ret); // Wire Call->Fun, Ret->CallEpi
    }
    return progress;
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds a edges in the graph
  // but NOT in the CG, until _cg_wired gets set.
  void wire1( GVNGCM gvn, CallNode call, Node fun, Node ret ) {
    assert _defs.find(ret)==-1; // No double wiring
    wire0(gvn,call,fun);
    // Wire self to the return
    gvn.add_work(this);
    if( gvn.check_out(this) ) add_def(      ret);
    else                  gvn.add_def(this, ret);
    gvn.add_work(ret);
    gvn.add_work_defs(call);
  }

  // Wire without the redundancy check, or adding to the CallEpi
  void wire0(GVNGCM gvn, CallNode call, Node fun) {
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
      TypeMem live = arg._live;
      switch( idx ) {
      case -1: actual = new ConNode<>(TypeRPC.make(call._rpc)); actual._live = live; break; // Always RPC is a constant
      case  0: actual = new MProjNode(call,Env.DEFMEM,CallNode.MEMIDX); break;    // Memory into the callee
      case  1: actual = new FP2ClosureNode(call); break; // Filter Function Pointer to Closure
      default: actual = idx >= call.nargs()              // Check for args present
          ? new ConNode<>(Type.ALL) // Missing args, still wire (to keep FunNode neighbors) but will error out later.
          : new ProjNode(idx+CallNode.MEMIDX, call); // Normal args
        live = TypeMem.ESCAPE;
        break;
      }
      if( gvn._opt_mode._CG ) actual._live = TypeMem.DEAD; // With Call Graph, be optimistic on liveness
      actual = gvn._opt_mode == GVNGCM.Mode.Opto ? gvn.new_gcp(actual) : gvn.xform(actual);
      gvn.add_def(arg,actual);
      actual._live = (TypeMem)actual._live.meet(live);
      gvn.add_work(actual);
    }

    // Add matching control to function via a CallGraph edge.
    Node callgrf = new CProjNode(call,0);
    callgrf = gvn._opt_mode == GVNGCM.Mode.Opto ? gvn.new_gcp(callgrf) : gvn.xform(callgrf);
    gvn.add_def(fun,callgrf);
  }

  // Merge call-graph edges, but the call-graph is not discovered prior to GCP.
  // If the Call's type includes all-functions, then the CallEpi must assume
  // unwired Returns may yet appear, and be conservative.  Otherwise it can
  // just meet the set of known functions.
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type tin0 = val(0);
    if( !(tin0 instanceof TypeTuple) )
      return tin0.oob();     // Weird stuff?
    TypeTuple tcall = (TypeTuple)tin0;
    if( tcall._ts.length <= CallNode.ARGIDX ) return tcall.oob(); // Weird stuff
    Type tcmem = call().mem().val();
    if( !(tcmem instanceof TypeMem) ) return tcmem.oob();
    TypeMem caller_mem = (TypeMem)tcmem;

    // Get Call result.  If the Call args are in-error, then the Call is called
    // and we flow types to the post-call.... BUT the bad args are NOT passed
    // along to the function being called.
    // tcall[0] = Control
    // tcall[1] = Memory passed around the functions.
    // tcall[2] = TypeFunPtr passed to FP2Closure
    // tcall[3+]= Arg types
    Type ctl = CallNode.tctl(tcall); // Call is reached or not?
    if( ctl != Type.CTRL && ctl != Type.ALL )
      return TypeTuple.CALLE.dual();
    TypeFunPtr tfptr= CallNode.ttfpx(tcall); // Peel apart Call tuple
    TypeMemPtr tescs= call().tesc(tcall);    // Peel apart Call tuple

    // Fidxes; if still in the parser, assuming calling everything
    BitsFun fidxs = tfptr==null || tfptr.is_forward_ref() ? BitsFun.FULL : tfptr.fidxs();
    // NO fidxs, means we're not calling anything.
    if( fidxs==BitsFun.EMPTY ) return TypeTuple.CALLE.dual();
    if( fidxs.above_center() ) return TypeTuple.CALLE.dual(); // Not resolved yet

    // Default memory: global worse-case scenario
    Node defnode = in(1);
    Type defmem = defnode.val();
    if( !(defmem instanceof TypeMem) ) defmem = defmem.oob(TypeMem.ALLMEM);

    // Any not-wired unknown call targets?
    if( fidxs!=BitsFun.FULL ) {
      // If fidxs includes a parent fidx, then it was split - currently exactly
      // in two.  If both children are wired, then proceed to merge both
      // children as expected; same if the parent is still wired (perhaps with
      // some children).  If only 1 child is wired, then we have an extra fidx
      // for a not-wired child.  If this fidx is really some unknown caller we
      // would have to get super conservative; but its actually just a recently
      // split child fidx.  If we get the RetNode via FunNode.find_fidx we suffer
      // the non-local progress curse.  If we get super conservative, we end up
      // rolling backwards (original fidx returned int; each split will only
      // ever return int-or-better).  So instead we "freeze in place".
      outerloop:
      for( int fidx : fidxs ) {
        int kids=0;
        for( int i=0; i<nwired(); i++ ) {
          int rfidx = wired(i)._fidx;
          if( fidx == rfidx ) continue outerloop; // Directly wired is always OK
          if( fidx == BitsFun.parent(rfidx) ) kids++; // Count wired kids of a parent fidx
        }
        if( BitsFun.is_parent(fidx) ) { // Child of a split parent, need both kids wired
          if( kids==2 ) continue;       // Both kids wired, this is ok
          return val();                  // "Freeze in place"
        }
        if( !opt_mode._CG )  // Before GCP?  Fidx is an unwired unknown call target
          { fidxs = BitsFun.FULL; break; }
        assert opt_mode==GVNGCM.Mode.Opto; // During GCP, still wiring, post GCP all are wired
      }
    }

    // Compute call-return value from all callee returns
    Type trez = Type.ANY;
    Type tmem = TypeMem.ANYMEM;
    if( fidxs == BitsFun.FULL ) { // Called something unknown
      trez = Type.ALL;            // Unknown target does worst thing
      tmem = defmem;
    } else {                    // All targets are known & wired
      for( int i=0; i<nwired(); i++ ) {
        RetNode ret = wired(i);
        if( fidxs.test_recur(ret._fidx) ) { // Can be wired, but later fidx is removed
          Type tret = ret.val();
          if( !(tret instanceof TypeTuple) ) tret = tret.oob(TypeTuple.RET);
          tmem = tmem.meet(((TypeTuple)tret).at(1));
          trez = trez.meet(((TypeTuple)tret).at(2));
        }
      }
    }
    TypeMem post_call = (TypeMem)tmem;

    // If no memory projection, then do not compute memory
    if( opt_mode!=GVNGCM.Mode.Parse && ProjNode.proj(this,1)==null )
      return TypeTuple.make(Type.CTRL,TypeMem.ANYMEM,trez);

    // Build epilog memory.

    // Approximate "live out of call", includes things that are alive before
    // the call but not flowing in.  Catches all the "new in call" returns.
    BitsAlias esc_out = esc_out(post_call,trez);
    TypeObj[] pubs = new TypeObj[defnode._defs._len];
    for( int i=1; i<pubs.length; i++ ) {
      boolean ein  = tescs._aliases.test_recur(i);
      boolean eout = esc_out       .test_recur(i);
      pubs[i] = live_out_gcp(ein,eout,caller_mem.at(i),post_call.at(i),opt_mode,defnode.in(i));
    }
    TypeMem tmem3 = TypeMem.make0(pubs);

    return TypeTuple.make(Type.CTRL,tmem3,trez);
  }

  static BitsAlias esc_out( TypeMem tmem, Type trez ) {
    if( trez == Type.XNIL || trez == Type.NIL ) return BitsAlias.EMPTY;
    if( trez instanceof TypeFunPtr ) trez = ((TypeFunPtr)trez)._disp;
    if( trez instanceof TypeMemPtr )
      return tmem.all_reaching_aliases(((TypeMemPtr)trez)._aliases);
    return TypeMemPtr.OOP0.dual().isa(trez) ? BitsAlias.NZERO : BitsAlias.EMPTY;
  }

  // If pre-GCP, must lift the types
  // as strong as the Parser, which is a join with default memory.
  private static TypeObj live_out_gcp(boolean esc_in, boolean esc_out, TypeObj pre, TypeObj post, GVNGCM.Mode opt_mode, Node dn ) {
    if( dn == null ) return null; // A never-made (on this pass) type
    Type tdn = dn.val();           // Get default type
    // Decide to take the pre-call or post-call value.
    TypeObj to = esc_in || esc_out ? (TypeObj)post.meet(pre) : pre;
    if( tdn == TypeObj.UNUSED || tdn == TypeObj.ANY ) return TypeObj.UNUSED; // If dead, then dead
    // After/During GCP, this is the value
    if( opt_mode._CG ) return to;
    // Before GCP, must use DefNode to keep types as strong as the Parser.
    if( !(dn instanceof MrgProjNode) ) // Some kind of constant.
      // TODO: Probably should just jam down mrgproj/new for these constants
      return tdn instanceof TypeObj ? (TypeObj)tdn : tdn.oob(TypeObj.ISUSED);
    // Else there is a New/MrgProj
    TypeObj tdef2 = ((MrgProjNode)dn).nnn()._crushed;
    return (TypeObj)to.join(tdef2); // Lift to the default worse-case the Parser assumed
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

  // Inline the CallNode.  All inputs and outputs to/from the Call and CallEpi
  // nodes are replaced with the called function 'leafs'.  Memory must maintain
  // the knowledge of the escape/no-escape split, so the entire inlined body is
  // visited to "lower" the types.
  private Node inline( GVNGCM gvn, int level, CallNode call, Node ctl, Node mem, Node rez, RetNode ret, int cuid ) {
    assert (level&1)==0; // Do not actually inline, if just checking that all forward progress was found
    assert nwired()==0 || nwired()==1; // not wired to several choices
    if( FunNode._must_inline == cuid ) // Assert an expected inlining happens
      FunNode._must_inline = 0;
    // Unwire any wired called function
    if( ret != null && nwired() == 1 && !ret.is_copy() ) // Wired, and called function not already collapsing
      unwire(gvn,call,ret);

    // Update memory in the body with the not-escaped values (which had
    // bypasses the body and now flow into it).
    Ary<Node> work = new Ary<>(new Node[1],0);
    MProjNode emprj = (MProjNode)ProjNode.proj(this,1);
    MProjNode cmprj = (MProjNode)ProjNode.proj(call,1);
    if( mem != call.mem() && cmprj !=null ) { // Most primitives do nothing with memory
      work.addAll(cmprj._uses);
      gvn.subsume(cmprj,call.mem());
      if( mem == cmprj ) mem = call.mem();
      // Update all memory ops
      while( !work.isEmpty() ) {
        Node wrk = work.pop();
        if( wrk.is_mem() ) {
          Type t2 = wrk.value(gvn._opt_mode); // Compute a new type
          if( !t2.isa(wrk.val()) ) { // Types out of alignment, need to forward progress here
            // Move types 'down' and add users to worklist.
            wrk.set_val(t2); // Move 'down', wrong direction, and recognize the escaped type is alive here
            assert !(wrk instanceof MProjNode && wrk.in(0) instanceof CallNode); // Should not push work outside the function
            work.addAll(wrk._uses);
          }
        }
        if( wrk instanceof CallNode ) { // Unless a Call which escape-filters; then need to check CallEpi as well
          CallEpiNode cepi = ((CallNode)wrk).cepi();
          if( cepi != null ) work.push(cepi);
        }
      }
    }

    // Sigh, ugly hack because Load/Stores are so strong.  All load/store
    // children of the inlined call need to hit the worklist.
    if( emprj != null ) {
      work.addAll(emprj._uses);
      while( !work.isEmpty() ) {
        Node wrk = work.pop();
        if( wrk.is_mem() ) {
          if( wrk instanceof LoadNode ) gvn.add_work(wrk);
          if( wrk instanceof StoreNode ) { gvn.add_work(wrk); work.addAll(wrk._uses); }
        }
      }
      gvn.subsume(emprj,mem);
    }

    // Move over Control
    CProjNode ccprj = (CProjNode)ProjNode.proj(call,0);
    if( ccprj != null ) gvn.subsume(ccprj,call.ctl());
    CProjNode ceprj = (CProjNode)ProjNode.proj(this,0);
    if( ceprj != null ) gvn.subsume(ceprj,ctl);
    else set_def(0,null,gvn);

    // Move over result
    if( !is_dead() ) {
      ProjNode reprj = ProjNode.proj(this,2);
      if( reprj != null ) gvn.subsume(reprj,rez);
    }

    // Move over arguments
    for( int i=0, idx; !call.is_dead() && i<call._uses._len; ) {
      Node use = call._uses.at(i);
      if( use instanceof ProjNode && (idx=((ProjNode)use)._idx) >= 2 ) {
        Node arg = call.arg(idx - CallNode.MEMIDX);
        if( rez==use ) rez = arg;
        gvn.subsume(use, arg);
      }
      else if( use instanceof FP2ClosureNode )
        gvn.set_def_reg(use,0,call.fun());
      else i++;
    }

    // While not strictly necessary, immediately fold any dead paths to
    // functions to clean up the CFG.
    rez.keep();
    while( !call.is_dead() ) {
      Node proj = call._uses.at(0);
      Node parm = proj._uses.at(0);
      gvn.xform_old(parm.in(0),0);
    }
    rez.unhook();

    assert gvn._opt_mode== GVNGCM.Mode.Parse || Env.START.more_flow(gvn,new VBitSet(),true,0)==0; // Check for sanity
    return rez;
  }

  void unwire(GVNGCM gvn, CallNode call, RetNode ret) {
    assert sane_wiring();
    if( !ret.is_copy() ) {
      FunNode fun = ret.fun();
      for( int i = 1; i < fun._defs._len; i++ ) // Unwire
        if( fun.in(i).in(0) == call ) {
          gvn.set_def_reg(fun, i, Env.XCTRL);
          break;
        }
      gvn.add_work_uses(fun);
    }
    gvn.add_work(ret);
    del(_defs.find(ret));
    assert sane_wiring();
  }

  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Compute local contribution of use liveness to this def.  If the call is
  // Unresolved, then none of CallEpi targets are (yet) alive.
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    assert _keep==0;
    // Not a copy
    if( def==in(0) ) return _live; // The Call
    if( def==in(1) ) return _live; // The DefMem
    // Wired return.
    // The given function is alive, only if the Call will Call it.
    Type tcall = call().val();
    if( !(tcall instanceof TypeTuple) ) return tcall.above_center() ? TypeMem.DEAD : _live;
    BitsFun fidxs = CallNode.ttfp(tcall).fidxs();
    int fidx = ((RetNode)def).fidx();
    if( fidxs.above_center() || !fidxs.test(fidx) )
      return TypeMem.DEAD;    // Call does not call this, so not alive.
    return _live;
  }

  @Override Node is_pure_call() { return in(0) instanceof CallNode ? call().is_pure_call() : null; }
  // Return the set of updatable memory - including everything reachable from
  // every call argument (including the display), and any calls reachable from
  // there, transitively through memory.
  //
  // In practice, just the no-escape aliases
  @Override BitsAlias escapees() { return BitsAlias.FULL; }
}
