package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
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
  public boolean _is_copy;
  public CallEpiNode( Node... nodes ) {
    super(OP_CALLEPI,nodes);
    Env.GVN.add_reduce(call());
    _live=RootNode.def_mem(this);
  }
  @Override public String xstr() {// Self short name
    if( _is_copy ) return "CopyEpi";
    if( is_dead() ) return "XallEpi";
    return "CallEpi";
  }
  @Override boolean is_CFG() { return !_is_copy; }
  @Override public boolean is_mem() { return true; }
  public CallNode call() { return (CallNode)in(0); }
  // True if this calls an external function, and so escapes all arguments
  boolean is_global() { return len()>1 && in(1)!=null; }
  public int nwired() { return _defs._len-2; }
  public RetNode wired(int x) { return (RetNode)in(x+2); }

  // True if all Call value fidxs are wired.  Monotonic.  Always true if Call
  // fidxs are above-center (no wiring required, these paths are never taken).
  // Always false if Call fidxs are FULL or otherwise infinite.  Can be extra
  // wired functions never called.  Post-Combo, must all be wired but dead
  // paths can be trimmed.
  public boolean is_all_wired() {
    Type tc = call()._val;
    BitsFun fidxs = CallNode.ttfp(tc).fidxs();
    if( fidxs.above_center() ) return true; // No path is taken
    if( fidxs==BitsFun.NALL ) return false; // Some unknown path is unwired
    // Post-combo, was all wired but some dead paths may have been removed.
    //if( AA.LIFTING && Combo.HM_FREEZE ) return true;
    int ncall=0;
    for( int i=0; i<nwired(); i++ )
      if( fidxs.test(wired(i)._fidx) ) // Verify each fidx is wired
        ncall++;
    if( is_global() ) ncall++;      // Generic external function wired
    return ncall==fidxs.bitCount(); // All is wired
  }


  @Override public Node ideal_reduce() {
    if( _is_copy ) return null;
    CallNode call = call();
    Type tc = call._val;
    if( !(tc instanceof TypeTuple tcall) ) return null;
    if( CallNode.tctl(tcall) != Type.CTRL ) return null; // Call not executable
    // Get calls resolved function.
    BitsFun fidxs = CallNode.ttfp(tcall).fidxs();

    // If the call's allowed functions excludes any wired, remove the extras
    if( !fidxs.test(BitsFun.ALLX) ) { // Shortcut
      for( int i = 0; i < nwired(); i++ ) {
        RetNode ret = wired(i);
        if( !fidxs.test_recur(ret.fidx()) ) { // Wired call not in execution set?
          assert !BitsFun.is_parent(ret.fidx());
          // Remove the edge.  Pre-GCP all CG edges are virtual, and are lazily
          // and pessimistically filled in by ideal calls.  During the course
          // of lifting types, some manifested CG edges are killed.
          // Post-GCP all CG edges are manifest, but types can keep lifting
          // and so CG edges can still be killed.
          unwire(call,ret);
          return Env.GVN.add_reduce(this); // Return with progress and go again
        }
      }
    }

    // See if we can wire any new fidxs directly between Call/Fun and Ret/CallEpi.
    // This *adds* edges, but enables a lot of shrinking via inlining.
    if( check_and_wire(false) ) return this;

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    if( nwired()==1 && fidxs.abit() != -1 ) { // Wired to 1 target
      RetNode ret = wired(0);                 // One wired return
      FunNode fun = ret.fun();
      if( fun != null && fun._defs._len==2 && // Function is only called by 1 (and not the unknown caller)
          call.err(true)==null &&             // And args are ok
          call.mem().in(0) != call &&   // Dead self-recursive
          fun.in(1)._uses._len==1 &&    // And only calling fun
          ret._live.isa(_live) &&       // Call and return liveness compatible
          !fun.noinline() ) {           // And not turned off
        assert fun.in(1).in(0)==call;   // Just called by us
        int idx = Env.SCP_0._defs.find(ret);
        if( idx!=-1 ) Env.SCP_0.del(idx);
        Node rmem = ret.mem();
        if( rmem==null ) rmem = call.mem();  // Pure function memory is a copy of call
        fun.set_is_copy();              // Collapse the FunNode into the Call
        Env.GVN.add_flow(call.fdx());   // FunPtr probably goes dead
        return set_is_copy(ret.ctl(), rmem, ret.rez()); // Collapse the CallEpi into the Ret
      }
    }

    if( call.err(true)!=null ) return null; // CallNode claims args in-error, do not inline

    // Replace a resolved
    Node fdx = call.fdx();
    if( fdx instanceof FreshNode frsh ) fdx = frsh.id();

    // Only inline wired single-target function with valid args.  CallNode wires.
    if( !is_all_wired() ) return null;
    int fidx = fidxs.abit();
    if( fidx <= 1 ) return null; // More than one choice

    // Call allows 1 function not yet inlined, sanity check it.
    if( nwired()!=1 ) return null; // More than 1 wired, inline only via FunNode
    int cnargs = call.nargs();
    RetNode ret = RetNode.get(fidx);
    if( ret==null ) return null;
    FunNode fun = ret.fun();
    if( fun._val != Type.CTRL ) return null;
    assert !fun.is_dead() && fun.nargs() == cnargs; // All checked by call.err

    // Check for several trivial cases that can be fully inlined immediately.
    Node cctl = call.ctl();
    Node cmem = call.mem();
    Node rctl = ret.ctl();      // Control being returned
    Node rmem = ret.mem();      // Memory  being returned
    Node rrez = ret.rez();      // Result  being returned
    boolean inline = !fun.noinline();
    // If the function does nothing with memory, then use the call memory directly.
    if( rmem==null || (rmem instanceof ParmNode && rmem.in(CTL_IDX) == fun) || rmem._val ==TypeMem.ANYMEM )
      rmem = cmem;
    // Check that function return memory and post-call memory are compatible
    if( !(_val instanceof TypeTuple ttval) ) return null;
    Type selfmem = ttval.at(MEM_IDX);
    if( !rmem._val.isa( selfmem ) )
      return null;

    // Check for zero-op body (id function)
    if( rrez instanceof ParmNode && rrez.in(CTL_IDX) == fun && cmem == rmem && inline )
      return unwire(call,ret).set_is_copy(cctl,cmem,call.arg(((ParmNode)rrez)._idx)); // Collapse the CallEpi

    // Check for constant body
    Type trez = rrez._val;
    if( trez.is_con() && rctl==fun && cmem == rmem && inline )
      return unwire(call,ret).set_is_copy(cctl,cmem,Node.con(trez));

    // Check for a 1-op body using only constants or parameters and no memory effects.
    boolean can_inline=!(rrez instanceof ParmNode) && rmem==cmem && inline;
    for( Node parm : rrez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(CTL_IDX) == fun) &&
          !(parm instanceof ConNode)
          )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rrez.copy(false); // Copy the entire function body
      ProjNode proj = ProjNode.proj(this,REZ_IDX);
      int path=1; while( fun.in(path).in(0)!=call ) path++;
      irez._live = proj==null ? Type.ALL : proj._live; // sharpen liveness to the call-site liveness
      for( Node in : rrez._defs )
        irez.add_def((in instanceof ParmNode parm && parm.in(CTL_IDX) == fun) ? in.in(path) : in);
      if( irez instanceof PrimNode prim ) prim._badargs = call._badargs;
      GVN.add_work_new(irez);
      GVN.add_reduce(fun);
      return unwire(call,ret).set_is_copy(cctl,cmem,irez);
    }

    // Check for a 1-op body that uses parms and returns ctrl and memory.
    if( ret.ctl() instanceof CProjNode ) {
      can_inline = true;
      Node prim = ret.ctl().in(0);
      // Return is all projections from the primitive
      if( rmem instanceof MProjNode && rmem.in(0)==prim &&
          rrez instanceof  ProjNode && rrez.in(0)==prim &&
          prim.in(CTL_IDX) == fun ) {
        // Prim inputs all from Parms
        for( int i=MEM_IDX; i<prim.len(); i++ )
          if( !(prim.in(i) instanceof ParmNode && prim.in(i).in(0)==fun) )
            { can_inline=false; break; }
        if( can_inline ) {
          Node prim2 = prim.copy(false);
          prim2.add_def(cctl);
          prim2.add_def(cmem);
          for( int i=DSP_IDX; i<prim.len(); i++ )
            prim2.add_def(ProjNode.proj(call,i));
          prim2.init();
          Node ctl2 = new CProjNode(prim2).init();
          Node mem2 = new MProjNode(prim2).init();
          Node rez2 = new  ProjNode(prim2,REZ_IDX).init();
          Env.GVN.add_reduce(fun);
          return unwire(call,ret).set_is_copy(ctl2,mem2,rez2);
        }
      }
    }


    return null;
  }

  // Used during GCP and Ideal calls to see if wiring is possible.
  // Return true if a new edge is wired
  public boolean check_and_wire(boolean is_combo) {
    if( !(_val instanceof TypeTuple) ) return false; // Collapsing
    CallNode call = call();
    Type tcall = call._val;
    if( !(tcall instanceof TypeTuple) ) return false;
    TypeFunPtr tfp = CallNode.ttfp(tcall);
    if( tfp.is_full() ) {       // Error call
      call.deps_add(call);      // If call-type changes, self can wire
      return false;
    }
    if( tfp.above_center() )  return false; // Still choices to be made during GCP.

    // Check all fidxs for being wirable
    boolean progress = false;
    for( int fidx : tfp.fidxs() ) { // For all fidxs
      if( BitsFun.is_parent(fidx) ) continue; // Do not wire parents, as they will eventually settle out
      RetNode ret = RetNode.get(fidx);        // Lookup, even if not wired
      if( ret==null || ret.is_copy() ) continue; // Dead or RootNode.EXT_FIDX
      if( _defs.find(ret) != -1 ) continue;   // Wired already
      FunNode fun = ret.fun();
      if( !CEProjNode.wired_arg_check(tcall,fun) ) continue; // Args fail basic sanity
      progress=true;
      wire1(call,fun,ret,is_combo); // Wire Call->Fun, Ret->CallEpi
    }
    if( progress && is_all_wired() )
      add_reduce_uses(); // Progress on pure memory uses
    return progress;
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.  
  void wire1( CallNode call, Node fun, Node ret, boolean is_combo ) {
    assert _defs.find(ret)==-1; // No double wiring
    wire0(call,fun,is_combo);
    if( len()==1 ) add_def(null); // Skip a slot for a future Root wire
    // Wire self to the return
    add_def(ret);
    GVN.add_flow(this);
    GVN.add_flow(call);
    call.add_flow_defs();
  }

  // Wire without the redundancy check, or adding to the CallEpi
  void wire0(CallNode call, Node fun, boolean is_combo) {
    // Wire.  Bulk parallel function argument path add
    Node cep = new CEProjNode(call);
    cep  = is_combo ? cep.init1() : Env.GVN.init(cep);
    fun.add_def(GVN.add_flow(cep));

    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) != fun || !(arg instanceof ParmNode parm) ) continue;
      Node actual = switch( parm._idx ) {
      case 0 -> new ConNode<>(TypeRPC.make(call._rpc)); // Always RPC is a constant
      case MEM_IDX -> new MProjNode(call); // Memory into the callee
      default -> parm._idx >= call.nargs() // Check for args present
      ? Env.ALL  // Missing args, still wire (to keep FunNode neighbors) but will error out later.
      : new ProjNode(call, parm._idx); // Normal args
      };
      actual = is_combo ? actual.init1() : Env.GVN.init(actual);
      arg.add_def(actual);
      actual.xliv();
      if( arg._val.is_con() ) // Added an edge, value may change or go in-error
        arg.add_flow_defs();  // So use-liveness changes
    }

    // Add matching control to function via a CallGraph edge.
    GVN.add_flow(fun);
    for( Node use : fun._uses ) GVN.add_flow(use);
    if( fun instanceof FunNode ) GVN.add_inline((FunNode)fun);
  }

  // Merge call-graph edges, but the call-graph is not discovered prior to GCP.
  // If the Call's type includes all-functions, then the CallEpi must assume
  // unwired Returns may yet appear, and be conservative.  Otherwise, it can
  // just meet the set of known functions.
  @Override public Type value() {
    if( _is_copy ) return _val; // A copy
    Type tin0 = val(0);
    if( !(tin0 instanceof TypeTuple tcall) )
      return tin0.oob(TypeTuple.CALLE); // Weird stuff?
    if( tcall._ts.length < ARG_IDX ) return tcall.oob(); // Weird stuff

    // Get Call result.  If the Call args are in-error, then the Call is called
    // and we flow types to the post-call.... BUT the bad args are NOT passed
    // along to the function being called.
    Type ctl = CallNode.tctl(tcall); // Call is reached or not?
    if( ctl != Type.CTRL && ctl != Type.ALL )
      return TypeTuple.CALLE.dual();
    TypeFunPtr tfptr= CallNode.ttfp(tcall);  // Peel apart Call tuple

    // If above_center (not resolved) or not all wired, can bail conservative
    BitsFun fidxs = tfptr.fidxs();
    if( fidxs.above_center() ) return TypeTuple.CALLE.dual();
    if( !is_all_wired() ) {    // Unknown callers?
      // Unknown callers call everything, touch everything.  Use Root memory.
      Env.ROOT.deps_add(this);
      TypeMem rmem = Env.ROOT.rmem();
      Type cmem = CallNode.emem(tcall);
      if( !Combo.HM_FREEZE ) Combo.add_freeze_dep(this);
      Type rfuns = is_global() ? Env.ROOT.ext_caller() : Type.ALL;
      return TypeTuple.make(Type.CTRL,rmem.meet(cmem),rfuns);
    }

    // Compute call-return value from all callee returns
    Type trez = Type.ANY;
    Type tmem = TypeMem.ANYMEM;
    if( !is_all_wired() ) {
      throw unimpl();           // Worse-case return from future unwired called fcns
    } else {
      if( is_global() ) {
        tmem = tmem.meet(Env.ROOT.rmem());
        trez = trez.meet(Env.ROOT.ext_caller());
        tmem = tmem.meet(CallNode.emem(tcall)); // Also get pass-thru memory
      }
      for( int i=0; i<nwired(); i++ ) { // For all wired calls
        RetNode ret = wired(i);
        if( !fidxs.test_recur(ret._fidx) ) continue;
        Type tret0 = ret._val;     // Get the called function return
        TypeTuple tret = (TypeTuple)(tret0 instanceof TypeTuple ? tret0 : tret0.oob(TypeTuple.RET));
        Type rmem = tret.at(MEM_IDX);
        if( ret.mem()==null ) // Pure call just passes memory thru
          rmem = CallNode.emem(tcall);
        tmem = tmem.meet(rmem);
        trez = trez.meet(tret.at(REZ_IDX));
      }
    }

    // Attempt to lift the result, based on HM types.  Walk the input HM type
    // and GCP flow type in parallel and create a mapping.  Then walk the
    // output HM type and CCP flow type in parallel, and join output CCP types
    // with the matching input CCP type.
    if( false && AA.DO_HMT )
      trez = hm_apply_lift(tvar(),trez);

    return TypeTuple.make(Type.CTRL,tmem,trez);
  }

  Type hm_apply_lift(TV3 rezt2, Type ret) {
    //// Walk the inputs, building a mapping
    //TV3.T2MAP.clear();
    //// Walk the display first, skipping through the function pointer to the display
    //TV3.WDUPS.clear();
    //TV3 tfun = call().fdx().tvar();
    //  if( tfun.is_fun() ) {
    //    TV3 dsp = tfun.get("2");
    //    if( dsp!=null )  dsp.walk_types_in(caller_mem,tfptr._dsp);
    //  }
    //  // Walk the args
    //  for( int i=ARG_IDX; i<call._defs._len-1; i++ )
    //    { TV3.WDUPS.clear(); call.tvar(i).walk_types_in(caller_mem,call.val(i)); }
    //  // Walk the outputs, building an improved result
    //  Type trez_sharp = tmem3.sharptr(trez);
    //  Type trez_lift = tvar().walk_types_out(trez_sharp,this);
    //  Type trez_lift_dull = trez_lift.simple_ptr();
    //  if( trez_lift instanceof TypeMemPtr )
    //    tmem3 = tmem3.lift_at((TypeMemPtr)trez_lift);  // Upgrade memory result
    //  trez = trez_lift_dull.join(trez);                // Upgrade scalar result
    // Turned off for now
    throw unimpl();
  }

  // Sanity check
  boolean sane_wiring() {
    CallNode call = call();
    for( int i=0; i<nwired(); i++ ) {
      RetNode ret = wired(i);
      if( ret.is_copy() ) return true; // Abort check, will be misaligned until dead path removed
      FunNode fun = ret.fun();
      boolean found=false;
      for( Node def : fun._defs )
        if( def instanceof CEProjNode && def.in(0)==call )
          { found=true; break; }
      if( !found ) return false;
    }
    return true;
  }

  @Override public Node is_copy(int idx) { return _is_copy ? in(idx) : null; }

  private CallEpiNode set_is_copy( Node ctl, Node mem, Node rez ) {
    CallNode call = call();
    if( FunNode._must_inline == call._uid ) // Assert an expected inlining happens
      FunNode._must_inline = 0;
    call._is_copy=_is_copy=true;
    Env.GVN.add_reduce_uses(call);
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
          Env.GVN.add_flow(fun);
          for( Node use : fun._uses ) {
            Env.GVN.add_flow(use); // Dead path, all Phis can lift
            Env.GVN.add_flow_defs(use); // All Phi uses lose a use
          }
          break;
        }
    }
    remove(_defs.find(ret));
    Env.GVN.add_reduce(ret);
    assert sane_wiring();
    return this;
  }

  // Compute local contribution of use liveness to this def.  If the call is
  // unresolved, then none of CallEpi targets are (yet) alive.
  @Override public Type live_use(Node def ) {
    if( _is_copy ) return def._live; // A copy
    // Not a copy
    if( def==in(0) ) return _live; // The Call
    if( def instanceof RetNode ret && ret.mem()==null ) return Type.ANY; // No memory input
    // Wired return.
    // The given function is alive, only if the Call will Call it.
    // This is morally equivalent to a Phi with dead control input declaring the value also dead.
    // It "turns around" value flow into liveness flow.
    Type tcall = call()._val;
    if( !(tcall instanceof TypeTuple) ) return tcall.above_center() ? Type.ANY : _live;
    BitsFun fidxs = CallNode.ttfp(tcall).fidxs();
    if( fidxs.above_center() ) return Type.ANY; // Not called, so not alive
    // Call does not call this, so not alive.
    if( def instanceof RetNode ret )
      return fidxs.test_recur(ret.fidx()) ? _live : Type.ANY;
    // Must be Root
    if( ((RootNode)def).rfidxs().overlaps(fidxs) )
      return _live;
    return Type.ANY;
  }

  @Override public boolean has_tvar() { return true; }

  // Same as HM.Apply.unify
  @Override public boolean unify( boolean test ) {
    assert !_is_copy;
    boolean progress = false;
    CallNode call = call();     // Call header for Apply
    Node fdx = call.fdx();      // node {dsp args -> ret}
    TV3 tv3 = fdx.tvar();       // type {dsp args -> ret}
    
    // Peek thru any error
    if( tv3 instanceof TVErr err ) tv3 = err.as_lambda();

    // If not one already, make a lambda term for the function.
    if( !(tv3 instanceof TVLambda tfun) ) {
      if( test ) return true;
      add_flow();           // Re-unify after forcing a Lambda, to get the args
      TVLambda lam = new TVLambda(call.nargs(),new TVLeaf(),tvar());
      if( tv3==null ) {
        // Error with no lambda, force one
        ((TVErr)fdx.tvar())._union_impl(lam);
        return true;
      }
      return tv3.unify(lam,false);
    }
    
    // Check for progress amongst args
    int tnargs = tfun.nargs() - ARG_IDX;
    int cnargs = call.nargs() - ARG_IDX;
    int nargs = Math.min(tnargs,cnargs);
    for( int i=DSP_IDX; i<nargs+ARG_IDX; i++ ) {
      TV3 formal = tfun.arg(i);
      TV3 actual = call.tvar(i);
      progress |= actual.unify(formal,test);
      if( progress && test ) return true;
    }

    // Check for progress on the return
    progress |= tvar().unify(tfun.ret(),test);

    
    if( tnargs > nargs )  // Missing arguments
      progress |= tvar().unify_err(test) | ((TVErr)tvar()).err_msg(("Passing "+cnargs+" arguments to a function taking "+tnargs+" arguments").intern(),test);
    if( cnargs > nargs ) throw unimpl(); // Too many arguments
    
    return progress;
  }

  private boolean bad_arg_cnt(boolean test) {
    TV3 self = tvar();
    if( self instanceof TVErr ) return false;
    if( !test ) {
      //self._err = "Bad argument count";
      //self.add_deps_work(work); // Error removes apply_lift
      throw unimpl();
    }
    return true;
  }

  // Unify trailing result ProjNode with the CallEpi directly.
  @Override public boolean unify_proj( ProjNode proj, boolean test ) {
    assert proj._idx==REZ_IDX;
    return tvar().unify(proj.tvar(),test);
  }

  // Return the set of updatable memory - including everything reachable from
  // every call argument (including the display), and any calls reachable from
  // there, transitively through memory.
  //
  // In practice, just the no-escape aliases
  //@Override BitsAlias escapees() { return BitsAlias.FULL; }
}
