package com.cliffc.aa.node;

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
  public CallEpiNode( Node... nodes ) { super(nodes); _live = TypeMem.ALLMEM; }
  @Override public String label() {// Self short name
    if( _is_copy ) return "CopyEpi";
    if( isDead() ) return "XallEpi";
    return "CallEpi";
  }
  @Override public boolean isMem() { return true; }
  @Override public boolean isMultiHead() { return true; }
  @Override public boolean isCFG() { return true; }
  @Override public Node isCopy(int idx) { return _is_copy ? in(idx) : null; }

  public CallNode call() { return (CallNode)in(0); }

  @Override public Node ideal_reduce() {
    if( _is_copy )
      return NodeUtil.fold_ccopy(this);
    CallNode call = call();
    Type tc = call._val;
    if( !(tc instanceof TypeTuple tcall) ) return null;

    // Wait until broken things clear out before wiring or inlining
    int len = len() - (last() instanceof RootNode ? 1 : 0);
    for( int i=1; i<len; i++ )
      if( ((RetNode)in(i)).isCopy() )
        return null;

    // Add or remove Call Graph edges according to fidxs
    Node progress = null;
    if( CG_wire() ) {
      _val = value();
      progress = this;
    }

    if( CallNode.tctl(tcall) != Type.CTRL ) return progress; // Call not executable

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    BitsFun fidxs = CallNode.ttfp(tcall).fidxs();
    if( !unknown_callers() && nwired()==1 && wired(0) instanceof RetNode ret && !ret.isPrim() && !call.isPrim() ) { // Wired to 1 target
      assert fidxs.abit() == ret._fidx; // Correct call graph
      FunNode fun = ret.fun();
      if( fun != null && fun.len()==2 && !fun.unknown_callers() && // Function is only called by 1 (and not the unknown caller)
          call.err(true)==null &&       // And args are ok
          call.mem().in(0) != call &&   // Dead self-recursive
          fun.in(1).nUses()==2 &&       // And only calling fun
          ret._live.isa(_live) &&       // Call and return liveness compatible
          !fun.noinline() ) {           // And not turned off
        assert fun.in(1)==call;         // Just called by us
        int idx = Env.SCP_0.findDef(ret);
        if( idx!=-1 ) Env.SCP_0.del(ret);
        Node rmem = ret.mem();
        if( rmem==null ) rmem = call.mem();  // Pure function memory is a copy of call
        Env.GVN.add_flow(call.fdx());   // FunPtr probably goes dead
        call.deps_work_clear();         // Other args to call might go dead
        fun.set_is_copy();              // Collapse the FunNode into the Call
        return set_is_copy(ret.ctl(), rmem, ret.rez()); // Collapse the CallEpi into the Ret
      }
    }

    if( call.err(true)!=null ) return progress; // CallNode claims args in-error, do not inline

    // Only inline wired single-target function with valid args.  CallNode wires.
    if( !is_CG(true) ) return progress;
    int fidx = fidxs.abit();
    if( fidx <= 1 ) return progress; // More than one choice

    // Call allows 1 function not yet inlined, sanity check it.
    if( nwired()!=1 ) return progress; // More than 1 wired, inline only via FunNode
    if( isPrim() ) return progress;    // Only inline via FunNode
    int cnargs = call.nargs();
    RetNode ret = RetNode.get(fidx);
    if( ret==null ) return progress;
    FunNode fun = ret.fun();
    if( fun._val != Type.CTRL ) return progress;
    assert !fun.isDead() && fun.nargs() == cnargs; // All checked by call.err

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
    if( !(_val instanceof TypeTuple ttval) ) return progress;
    Type selfmem = ttval.at(MEM_IDX);
    if( !rmem._val.isa( selfmem ) )
      return progress;

    // Check for zero-op body (id function)
    if( rrez instanceof ParmNode && rrez.in(CTL_IDX) == fun && cmem == rmem && inline )
      return unwire(call,ret,fun).set_is_copy(cctl,cmem,call.arg(((ParmNode)rrez)._idx)); // Collapse the CallEpi

    // Check for constant body
    Type trez = rrez._val;
    if( trez.is_con() && rctl==fun && cmem == rmem && inline ) {
      Node c = Node.con(trez);
      c._live = Type.ALL;
      return unwire(call,ret,fun).set_is_copy(cctl,cmem,c);
    }

    // Check for a 1-op body using only constants or parameters and no memory effects.
    boolean can_inline=!(rrez instanceof ParmNode) && rmem==cmem && inline;
    for( Node parm : rrez.defs() )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(CTL_IDX) == fun) &&
          !(parm instanceof ConNode)
          )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rrez.copy(false); // Copy the entire function body
      ProjNode proj = ProjNode.proj(this,REZ_IDX);
      irez._live = proj==null ? Type.ALL : proj._live; // sharpen liveness to the call-site liveness
      for( Node in : rrez.defs() )
        irez.addDef((in instanceof ParmNode parm && parm.in(CTL_IDX) == fun) ? call.arg(parm._idx) : in);
      if( irez instanceof PrimNode prim ) prim._badargs = call._badargs;
      GVN.add_work_new(irez);
      GVN.add_reduce(fun);
      return unwire(call,ret,fun).set_is_copy(cctl,cmem,irez);
    }

    // Check for a 1-op body that uses parms and returns ctrl and memory.
    if( ret.ctl() instanceof CProjNode ) {
      can_inline = true;
      Node prim = ret.ctl().in(0);
      // Return is all projections from the primitive
      if( rmem instanceof MProjNode && rmem.in(0)==prim &&
          rrez instanceof  ProjNode && rrez.in(0)==prim &&
          prim.in(CTL_IDX) == fun ) {
        //// Prim inputs all from Parms
        //for( int i=MEM_IDX; i<prim.len(); i++ )
        //  if( !(prim.in(i) instanceof ParmNode && prim.in(i).in(0)==fun) )
        //    { can_inline=false; break; }
        //if( can_inline ) {
        //  Node prim2 = prim.copy(false);
        //  prim2.add_def(cctl);
        //  prim2.add_def(cmem);
        //  for( int i=DSP_IDX; i<prim.len(); i++ )
        //    prim2.add_def(ProjNode.proj(call,i));
        //  prim2.init();
        //  Node ctl2 = new CProjNode(prim2).init();
        //  Node mem2 = new MProjNode(prim2).init();
        //  Node rez2 = new  ProjNode(prim2,REZ_IDX).init();
        //  Env.GVN.add_reduce(fun);
        //  return unwire(call,ret,fun).set_is_copy(ctl2,mem2,rez2);
        //}
        throw TODO();
      }
    }

    return progress;
  }

  // Merge call-graph edges, but the call-graph is not discovered prior to GCP.
  // If the Call's type includes all-functions, then the CallEpi must assume
  // unwired Returns may yet appear, and be conservative.  Otherwise, it can
  // just meet the set of known functions.
  @Override public Type value() {
    if( _is_copy ) return _val; // A copy
    Type tin0 = val(0);
    if( !(tin0 instanceof TypeTuple tcall) || call().len() != tcall.len() )
      return tin0.oob(TypeTuple.CALLE); // Weird stuff?

    // Get Call result.  If the Call args are in-error, then the Call is called
    // and we flow types to the post-call.... BUT the bad args are NOT passed
    // along to the function being called.
    Type ctl = CallNode.tctl(tcall); // Call is reached or not?
    if( ctl != Type.CTRL && ctl != Type.ALL )
      return TypeTuple.CALLE.dual();
    TypeFunPtr tfptr= CallNode.ttfp(tcall);  // Peel apart Call tuple

    // If above_center (not resolved) or not all wired, can bail conservative
    BitsFun fidxs = tfptr.fidxs();
    if( Combo.pre() && fidxs.above_center() ) return TypeTuple.CALLE.dual();
    if( Combo.pre() &&           // In iter (not combo)
        (fidxs==BitsFun.EMPTY || // Lifted to no functions
         len()==1 ||             // Not wired (wireable?)
         !is_CG(true)) )         // Unknown callers?
      return TypeTuple.make(Type.CTRL,RootNode.defMem(this),Type.ALL); // Unknown callers return e.g. error states

    assert is_CG(false);

    // Pre-Combo:
    // - fidxs are conservative, and may get removed, and may be e.g. BitsFun.NALL, or may go above center.
    // - If we get here, we have a conservative set of wired fidxs that are not NALL (checked above).
    // - If we get here, its conservative correct to meet across returns &
    //   mixing in the pre-call is required for root or pure calls
    assert !(Combo.pre() && fidxs==BitsFun.NALL);

    // Combo:
    // - fidxs are optimistic, and may get added, and start above center and may fall to NALL.
    // - Above center ones do not wire, so this loop is empty then.
    // - Might fall through some middle fidxs, then hit NALL.  Middle fidxs wire, and are precise.
    // - NALL requires mixing in Root defMem
    if( !Combo.pre() && fidxs==BitsFun.NALL )
      return TypeTuple.make(Type.CTRL,Env.ROOT.rmem(this).meet(CallNode.emem(tcall)),tfptr._ret); // Error state

    // Post-Combo:
    // - fidxs are conservative, may get removed, and will not be NALL (checked above).
    // - If we get here, its conservative correct to meet across returns &
    //   mixing in the pre-call is required for root or pure calls

    // Compute meet over wired called function returns.
    Type tmem = TypeMem.ANYMEM, rmem;
    Type trez = fidxs.above_center() || nwired()==0 ? tfptr._ret : Type.ANY, rrez;
    int fidx;
    for( int i=1; i<len(); i++ ) {
      if( in(i) instanceof RetNode ret ) {
        fidx = ret._fidx;
        TypeTuple tret = ret._val instanceof TypeTuple tt ? tt : (TypeTuple)ret._val.oob(TypeTuple.RET);
        rmem = tret.at(MEM_IDX);
        rrez = tret.at(REZ_IDX);
      } else {                  // Calling Root, taking Root return value
        assert in(i)==Env.ROOT;
        fidx = BitsFun.EXTX;
        rmem = Env.ROOT.rmem(this);
        rrez = Env.ROOT.ext_caller();
      }
      if( !fidxs.test_recur(fidx) ) continue;
      tmem = tmem.meet(rmem);
      trez = trez.meet(rrez);
    }
    tmem = tmem.meet(CallNode.emem(tcall));

    // Attempt to lift the result, based on HM types.  Walk the input HM type
    // and GCP flow type in parallel and create a mapping.  Then walk the
    // output HM type and CCP flow type in parallel, and join output CCP types
    // with the matching input CCP type.
    if( false && DO_HMT )
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
    throw TODO();
  }

  CallEpiNode unwire(CallNode call, Node ret, Node fun) {
    assert is_CG(true);
    del(ret);
    fun.del(call);
    GVN.add_flow_uses(fun); // One less caller of function, parms can lift
    GVN.add_flow(fun);
    return this;
  }

  private CallEpiNode set_is_copy( Node ctl, Node mem, Node rez ) {
    assert !isPrim();
    CallNode call = call();
    if( FunNode._must_inline == call._uid ) // Assert an expected inlining happens
      FunNode._must_inline = 0;
    call._is_copy=_is_copy=true;
    call.pop();                 // Drop call fdx; other args need to be copied-thru
    Env.GVN.add_reduce_uses(call);
    Env.GVN.add_reduce_uses(this);
    ctl.keep();
    mem.keep();
    rez.keep();
    while( len()>0 ) pop();
    addDef(ctl.unkeep());
    addDef(mem.unkeep());
    addDef(rez.unkeep());
    return this;
  }

  // Call Graph API:

  // - After Combo, the CG is explicit.  All CallEpis have an edge to their
  //   Call in slot 0, some edges to RetNodes in slots 1-n, and an edge to Root
  //   if called externally.
  // - Pre-Combo, if FDX is NALL all edges are implicit.  As FDX tightens up,
  //   explicit CG edges are added - and remain conservatively correct forever.
  // - If FDX includes BitsFun.EXTX, an edge to Root is added in the last position.
  // - If any CG edge is explicit, all are.
  //

  public int nwired() { return len()-1; }
  public Node wired(int x) { return in(x+1); }

  // True if this CallEpi has virtual CG edges to other unknown callees.
  // If any function is wired, all are.
  boolean unknown_callers() { return len()==1 || isPrim(); }

  // Checks for sane Call Graph, similar to RetNode.is_CG
  public boolean is_CG(boolean precise) {
    CallNode call = call();
    BitsFun fidxs = call.tfp()._fidxs;
    // Check back edges from CEPI to CALL
    for( int i=1; i<len(); i++ ) {
      int fidx;
      Node n = in(i);
      if( n instanceof RetNode ret ) {
        fidx = ret._fidx;
        n = ret.fun();
      } else {                  // Root is always last, if it appears at all
        if( !(n instanceof RootNode) || i!=len()-1) return false;
        fidx = BitsFun.EXTX;
      }
      if( (!LIFTING || precise) && // During Combo or after correcting during Iter,
          !fidxs.test(fidx) ) return false; // wired without matching fidx is an error
      if( n.findDef(call) == -1 ) return false; // Wired below but not above
    }
    // Check forward edges from CALL to CEPI
    for( int i=0; i<call.nUses(); i++ ) {
      Node use = call.use(i);
      if( use==this ) continue;
      if( use instanceof FunNode fun ) use = fun.ret();
      if( findDef(use) == -1 )
        return false;           // Wired above but not below
    }
    if( fidxs==BitsFun.NALL ) return !precise; // Some kind of error condition
    // If precise, check that every fidx is wired.  If not precise we might
    // have fidxs not yet wired.
    if( precise && !fidxs.above_center() ) {
      for( int fidx : fidxs ) {
        if( fidx == BitsFun.EXTX ) {
          if( last()!=Env.ROOT ) return false;
        } else {
          RetNode ret = RetNode.get(fidx);
          if( ret!=null && !ret.isCopy() && findDef(ret)== -1 && ret.fun().nargs()==call.nargs())
            return false;
        }
      }
    }

    return true;                // Everything is OK
  }

  // Used during GCP and Ideal calls to see if wiring is possible.
  // Return true if a new edge is wired
  public boolean CG_wire() {
    assert !_is_copy && is_CG(false);        // Might be imprecise, but conservatively correct
    boolean progress = false;

    CallNode call = call();
    TypeFunPtr tfp = call.tfp();
    BitsFun fidxs = tfp._fidxs;
    if( fidxs==BitsFun.NALL ) return false;
    // Remove extra wires (mostly post-combo)
    for( int i=1; i<len(); i++ ) {
      int fidx = in(i) instanceof RetNode ret ? ret._fidx : BitsFun.EXTX;
      boolean ok_nargs = !(in(i) instanceof RetNode ret) || (call.nargs()== ret.fun().nargs());
      if( fidxs.above_center() || !fidxs.test_recur(fidx) || !ok_nargs ) {
        progress=true;
        Env.GVN.add_flow(call);
        if( fidx==BitsFun.EXTX ) {
          Env.ROOT.del(call);
          pop();                // Remove wire to Root
        } else {
          FunNode fun = ((RetNode)in(i)).fun();
          fun.add_flow_uses();  // Parms merge fewer
          Env.GVN.add_reduce(in(i)); // Fewer uses of Ret
          //fun.remove(call);     // Remove from Fun
          //remove(in(i));        // Remove from Ret
          //i--;
          throw TODO();         // Make sure fun parms in-sync
        }
      }
    }

    // Add missing wires
    boolean vCG = unknown_callers(); // Has virtual CG edges
    if( !fidxs.above_center() ) {
      for( int fidx : fidxs ) {
        Node ret,fun;
        if( fidx == BitsFun.EXTX ) {
          ret = fun = Env.ROOT;
        } else {
          RetNode ret2 = RetNode.get(fidx);
          if( ret2==null || ret2.isCopy() ) continue;
          FunNode fun2 = ret2.fun();
          if( fun2==null ) continue; // Broken function
          if( call.nargs() != fun2.nargs() ) continue; // Mismatched
          ParmNode mem = fun2.parm(MEM_IDX);
          if( mem != null ) {
            // Call liveness are already meeting EXTMEM.
            // We can wire if the meet-over-all-wired liveness is below the current liveness.
            //TypeMem mlive = (TypeMem)mem._live.meet(TypeMem.EXTMEM);
            Type mlive = mem._live.meet(TypeMem.ANYMEM);
            if(  LIFTING && !mlive.isa(call._live) ) return progress;
          }
          ret = ret2; fun = fun2;
        }
        if( findDef(ret) != -1  ) continue; // Already present
        assert vCG || !Combo.pre(); // Only add 1 time when going from virtual to concrete Call Graph; during Combo edges are added lazily
        progress = true;
        // Add edge from CallEpi to Ret
        addDef(ret);
        fun.addDef(call);
        Env.GVN.add_flow(fun);
        Env.GVN.add_flow_uses(fun);    // Parms have new inputs
        Env.GVN.add_reduce(fun); // Last caller wired
        // Swap so ROOT remains last
        if(     in(    len()-2)==Env.ROOT )     swap_last();
        if( fun.in(fun.len()-2)==Env.ROOT ) fun.swap_last();
        if( fun instanceof FunNode fun2 ) Env.GVN.add_inline(fun2);
        assert !unknown_callers(); // Only add 1 time when going from virtual to concrete Call Graph
      }
    } else {
      call.deps_add(call);      // Call type sharpens, can wire
    }
    if( progress ) GVN.add_flow_defs(GVN.add_flow(call)); // Call, args may change liveness
    assert is_CG(true );        // Precise
    return progress;            //
  }


  @Override public Type live() {
    return _is_copy ? _live : super.live(); // Freeze in place if dying
  }

  // Compute local contribution of use liveness to this def.  If the call is
  // unresolved, then none of CallEpi targets are (yet) alive.
  @Override public Type live_use( int i ) {
    Node def = in(i);
    if( _is_copy ) {            // A copy
      if( isKeep() ) return def._live;
      ProjNode p = ProjNode.proj(this,i);
      if( p==null ) return Type.ANY;
      p.deps_add(in(i));
      return p._live;
    }
    // Not a copy
    if( i==CTL_IDX ) return _live;
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
  @Override public TV3 _set_tvar() {
    // Unwire all; will rewire optimistically during Combo
    while( nwired()>0 ) {
      Node w = popKeep(), fun=w;
      if( w instanceof RetNode ret ) fun = ret.fun();
      fun.del(call());
    }
    assert is_CG(false);

    _tvar = new TVLeaf();
    CallNode call = call();     // Call header for Apply
    Node fdx = call.fdx();      // node {dsp dyn args -> ret}
    TV3 tfun = fdx.set_tvar();  // type {dsp dyn args -> ret}
    
    TVLambda lam = tfun instanceof TVLambda lam0 ? lam0
      : new TVLambda(call.nargs(),new TVLeaf(),tvar());
    if( !(tfun instanceof TVLambda) )
      tfun.unify(lam,false);
      
    assert lam.nargs() == call.nargs();
    for( int i=DSP_IDX; i<call.nargs(); i++ ) {
      TV3 targ = call.in(i).set_tvar();
      lam = (TVLambda)lam.find();
      if( lam.arg(i) != null )
        lam.arg(i).unify( targ, false );
    }
    tvar().unify(lam.ret(),false);
    return tvar();
  }
  // Unify trailing result ProjNode with the CallEpi directly.
  @Override public TV3 unify_proj( ProjNode proj ) {
    if( proj._idx==REZ_IDX )
      return set_tvar();
    throw TODO();
  }

}
