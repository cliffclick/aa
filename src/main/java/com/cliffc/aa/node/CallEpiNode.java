package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.Env.GVN;

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
  boolean _is_copy;
  public CallEpiNode( Env e, Node... nodes ) {
    super(OP_CALLEPI,nodes);
    assert nodes[1] instanceof DefMemNode;
  }
  @Override public String xstr() {// Self short name
    if( _is_copy ) return "CopyEpi";
    if( is_dead() ) return "XallEpi";
    return "CallEpi";
  }
  public CallNode call() { return (CallNode)in(0); }
  @Override public boolean is_mem() { return true; }
  int nwired() { return _defs._len-2; }
  RetNode wired(int x) { return (RetNode)in(x+2); }

  @Override public Node ideal_reduce() {
    if( _is_copy ) return null;
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
          unwire(call,ret);
          return this; // Return with progress
        }
      }
    }

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
        fun.set_is_copy();              // Collapse the FunNode into the Call
        return set_is_copy(ret.ctl(), ret.mem(), ret.rez()); // Collapse the CallEpi into the Ret
      }
    }

    // Parser thunks eagerly inline
    if( call.fdx() instanceof ThretNode ) {
      ThretNode tret = (ThretNode)call.fdx();
      wire1(call,tret.thunk(),tret);
      return set_is_copy(tret.ctrl(), tret.mem(), tret.rez());     // Collapse the CallEpi into the Thret
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
        if( idx < 0 ) continue; // RPC
        Type actual = CallNode.targ(tcall,idx);
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
    if( (rmem instanceof ParmNode && rmem.in(CTL_IDX) == fun) || rmem.val() ==TypeMem.XMEM )
      rmem = cmem;
    // Check that function return memory and post-call memory are compatible
    if( !(val() instanceof TypeTuple) ) return null;
    Type selfmem = ((TypeTuple) val()).at(MEM_IDX);
    if( !rmem.val().isa( selfmem ) && !(selfmem==TypeMem.ANYMEM && call.is_pure_call()!=null) )
      return null;

    // Check for zero-op body (id function)
    if( rrez instanceof ParmNode && rrez.in(CTL_IDX) == fun && cmem == rmem && inline )
      return unwire(call,ret).set_is_copy(cctl,cmem,call.arg(((ParmNode)rrez)._idx)); // Collapse the CallEpi

    // Check for constant body
    Type trez = rrez.val();
    if( trez.is_con() && rctl==fun && cmem == rmem && inline )
      return unwire(call,ret).set_is_copy(cctl,cmem,Node.con(trez));

    // Check for a 1-op body using only constants or parameters and no memory effects
    boolean can_inline=!(rrez instanceof ParmNode) && rmem==cmem && inline;
    for( Node parm : rrez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rrez.copy(false); // Copy the entire function body
      ProjNode proj = ProjNode.proj(this,REZ_IDX);
      irez._live = proj==null ? TypeMem.ESCAPE : proj._live;
      for( Node parm : rrez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(CTL_IDX) == fun) ? call.arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = call._badargs;
      GVN.add_work_all(irez);
      return unwire(call,ret).set_is_copy(cctl,cmem,irez);
    }

    return null;
  }

  // See if we can wire any new fidxs directly between Call/Fun and Ret/CallEpi
  @Override public Node ideal_mono() {
    if( _is_copy ) return null; // A copy
    return check_and_wire() ? this : null;
  }

  @Override public Node ideal(GVNGCM gvn, int level) { throw unimpl(); }

  // Used during GCP and Ideal calls to see if wiring is possible.
  // Return true if a new edge is wired
  public boolean check_and_wire( ) {
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
      wire1(call,fun,ret);      // Wire Call->Fun, Ret->CallEpi
    }
    return progress;
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  This adds a edges in the graph
  // but NOT in the CG, until _cg_wired gets set.
  void wire1( CallNode call, Node fun, Node ret ) {
    assert _defs.find(ret)==-1; // No double wiring
    wire0(call,fun);
    // Wire self to the return
    add_def(ret);
    if( fun instanceof FunNode ) GVN.add_inline((FunNode)fun);
  }

  // Wire without the redundancy check, or adding to the CallEpi
  void wire0(CallNode call, Node fun) {
    // Wire.  Bulk parallel function argument path add

    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) != fun || !(arg instanceof ParmNode) ) continue;
      // See CallNode output tuple type for what these horrible magic numbers are.
      Node actual;
      int idx = ((ParmNode)arg)._idx;
      switch( idx ) {
      case -1: actual = new ConNode<>(TypeRPC.make(call._rpc)); break; // Always RPC is a constant
      case MEM_IDX: actual = new MProjNode(call,Env.DEFMEM); break;    // Memory into the callee
      default: actual = idx >= call.nargs()              // Check for args present
          ? new ConNode<>(Type.ALL) // Missing args, still wire (to keep FunNode neighbors) but will error out later.
          : new ProjNode(call,idx); // Normal args
        break;
      }
      arg.add_def(actual.init1());
    }

    // Add matching control to function via a CallGraph edge.
    fun.add_def(new CProjNode(call).init1());
    GVN.add_flow(fun);
    if( fun instanceof ThunkNode ) GVN.add_reduce_uses(fun);
  }

  // Merge call-graph edges, but the call-graph is not discovered prior to GCP.
  // If the Call's type includes all-functions, then the CallEpi must assume
  // unwired Returns may yet appear, and be conservative.  Otherwise it can
  // just meet the set of known functions.
  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( _is_copy ) return _val; // A copy
    Type tin0 = val(0);
    if( !(tin0 instanceof TypeTuple) )
      return tin0.oob();     // Weird stuff?
    TypeTuple tcall = (TypeTuple)tin0;
    if( tcall._ts.length < ARG_IDX ) return tcall.oob(); // Weird stuff

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
          tmem = tmem.meet(((TypeTuple)tret).at(MEM_IDX));
          trez = trez.meet(((TypeTuple)tret).at(REZ_IDX));
        }
      }
    }
    TypeMem post_call = (TypeMem)tmem;

    // Lift result according to H-M typing
    TVar tv = tvar();
    if( tv instanceof TArgs && trez != Type.ALL ) // If already an error term, poison, stay error.
      trez = unify_lift(trez,((TArgs)tv).parm(2));

    // If no memory projection, then do not compute memory
    if( _keep==0 && ProjNode.proj(this,1)==null )
      return TypeTuple.make(Type.CTRL,TypeMem.ANYMEM,trez);

    // Build epilog memory.

    // Approximate "live out of call", includes things that are alive before
    // the call but not flowing in.  Catches all the "new in call" returns.
    BitsAlias esc_out = esc_out(post_call,trez);
    TypeObj[] pubs = new TypeObj[defnode._defs._len];
    TypeMem caller_mem = CallNode.emem(tcall); // Call memory
    for( int i=1; i<pubs.length; i++ ) {
      boolean ein  = tescs._aliases.test_recur(i);
      boolean eout = esc_out       .test_recur(i);
      TypeObj pre = caller_mem.at(i);
      TypeObj obj = ein || eout ? (TypeObj)(pre.meet(post_call.at(i))) : pre;
      if( !opt_mode._CG )       // Before GCP, must use DefMem to keeps types strong as the Parser
        obj = (TypeObj)obj.join(((TypeMem)defmem).at(i));
      pubs[i] = obj;
    }
    TypeMem tmem3 = TypeMem.make0(pubs);

    // Lift memory according to H-M typing
    Type tmem4 = tv instanceof TArgs ? unify_lift(tmem3,((TArgs)tv).parm(1)) : tmem3;

    return TypeTuple.make(Type.CTRL,tmem4,trez);
  }

  static BitsAlias esc_out( TypeMem tmem, Type trez ) {
    if( trez == Type.XNIL || trez == Type.NIL ) return BitsAlias.EMPTY;
    if( trez instanceof TypeFunPtr ) trez = ((TypeFunPtr)trez)._disp;
    if( trez instanceof TypeMemPtr )
      return tmem.all_reaching_aliases(((TypeMemPtr)trez)._aliases);
    return TypeMemPtr.OOP0.dual().isa(trez) ? BitsAlias.NZERO : BitsAlias.EMPTY;
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

  @Override public Node is_copy(int idx) { return _is_copy ? in(idx) : null; }

  private CallEpiNode set_is_copy( Node ctl, Node mem, Node rez ) {
    if( FunNode._must_inline == call()._uid ) // Assert an expected inlining happens
      FunNode._must_inline = 0;
    call()._is_copy=_is_copy=true;
    Env.GVN.add_reduce_uses(call());
    Env.GVN.add_reduce_uses(this);
    while( _defs._len>0 ) pop();
    add_def(ctl);
    add_def(mem);
    add_def(rez);
    return this;
  }

  CallEpiNode unwire(CallNode call, RetNode ret) {
    assert sane_wiring();
    if( !ret.is_copy() ) {
      FunNode fun = ret.fun();
      for( int i = 1; i < fun._defs._len; i++ ) // Unwire
        if( fun.in(i).in(0) == call ) {
          fun.set_def(i, Env.XCTRL);
          break;
        }
    }
    del(_defs.find(ret));
    reset_tvar();
    unify(false);
    assert sane_wiring();
    return this;
  }

  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Compute local contribution of use liveness to this def.  If the call is
  // Unresolved, then none of CallEpi targets are (yet) alive.
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    assert _keep==0 || _live==all_live();
    if( _is_copy ) return def._live; // A copy
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

  @Override public boolean unify( boolean test ) {
    if( _is_copy ) return false; // A copy
    // Build a HM tvar (args->ret), same as HM.java Apply does.  Instead of
    // grabbing a 'fresh' copy of 'Ident' (see HM.java) we grab it fresh at the
    // use point below, by calling 'fresh_unify' which acts as-if a fresh copy
    // is made, and then unifies it.
    Node fdx = call().fdx();
    TVar tfunv = fdx.tvar();
    if( tfunv instanceof TVDead ) return false; // Not gonna be a TFun
    if( !(tfunv instanceof TFun) )              // Progress
      return test || tfunv.unify(new TFun(fdx,null,new TVar(),new TVar()),false);
    // Actual progress only if the structure changes.
    //if( !((TFun)tfunv).fresh_unify(call().tvar(),tvar(),test,this) )
    //  return false;
    //if( !test )
    //  for( Node cuse : call()._uses ) // If Call transitions from TVar to TArgs
    //    TNode.add_work(cuse);         // Add proj users
    //return true;
    return false;
  }

  // H-M typing demands all unified Nodes have the same type... which is a
  // ASSERT/JOIN.  Hence the incoming type can be lifted to the join.
  private Type unify_lift(Type t, TVar tv) {
    if( tv._ns == null || tv._ns._len==0 ) return t;
    // TODO: DISABLED FOR NOW, STILL SORTING OUT
    //Type t2 = t;
    //for( int i=0; i<tv._ns._len; i++ ) {
    //  TNode tn = tv._ns.at(i);
    //  // Most of the unified Nodes are dead, unified because ideal() replaced
    //  // them with another.  However, their Types do not update after the merge
    //  // and become stale.  So no unify with the dead.
    //  if( tn.is_dead() ) tv._ns.remove(i--);
    //  else if( tn instanceof ProjNode && ((ProjNode)tn).in(0)==this ) /*self projection: do nothing*/;
    //  else {
    //    Type t3 = tn.val();
    //    Type t4 = tn instanceof MemSplitNode ? ((TypeTuple)t3).at(0) : t3;
    //    Type t5 = t4.widen();
    //    t2 = t2.join(t5);
    //  }
    //}
    //return t2;
    return t;
  }


  @Override Node is_pure_call() { return in(0) instanceof CallNode ? call().is_pure_call() : null; }
  // Return the set of updatable memory - including everything reachable from
  // every call argument (including the display), and any calls reachable from
  // there, transitively through memory.
  //
  // In practice, just the no-escape aliases
  @Override BitsAlias escapees() { return BitsAlias.FULL; }
}
