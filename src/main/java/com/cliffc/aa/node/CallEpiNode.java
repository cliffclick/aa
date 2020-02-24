package com.cliffc.aa.node;

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

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;

    CallNode call = call();
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    if( tcall.at(0) != Type.CTRL ) return null; // Call not executable
    Type tfptr = tcall.at(3);
    if( !(tfptr instanceof TypeFunPtr) ) return null; // No known function pointer
    TypeFunPtr tfp = (TypeFunPtr)tfptr;

    // The one allowed function is already wired?  Then directly inline.
    // Requires this calls 1 target, and the 1 target is only called by this.
    BitsFun fidxs = tfp.fidxs();
    if( nwired()==1 && fidxs.abit() != -1 ) { // Wired to 1 target
      RetNode ret = wired(0);                 // One wired return
      if( ret.fun()._defs._len==2 ) {         // Function is only called by 1 (and not the unknown caller)
        assert ret.fun().in(1).in(0)==call;   // Just called by us
        // Merge call-bypass memory and function memory.  Every above-center
        // alias "loses" to a below-center alias.  Below-center ties go to the
        // last mutator which is the return, above-center ties to the call.
        Node cmem = call.mem();
        Node rmem =  ret.mem();
        TypeMem call_mem = (TypeMem)gvn.type(cmem);
        TypeMem  ret_mem = (TypeMem)gvn.type(rmem);
        Node mem;
        if( ret_mem==TypeMem.XMEM ) {
          mem = cmem;           // Common shortcut for primitives
        } else if( call_mem==TypeMem.XMEM ) {
          mem = rmem;           // Common shortcut for simple calls
        } else {
          // Actually merge memories from call-bypass and post-call.  If one of
          // cmem or rmem is itself a MemMerge we'll get stacked MemMerges
          // which will clean out later.
          TypeObj[]  ret_objs =  ret_mem.alias2objs();
          TypeObj[] call_objs = call_mem.alias2objs();
          int max = Math.max(ret_objs.length,call_objs.length);
          // Alias#1 to make the merge
          MemMergeNode mmem = new MemMergeNode(ret_objs[1].above_center() ? cmem : rmem);
          // Merge all other aliases
          for( int i=2; i<max; i++ )
            if( (i<call_objs.length && call_objs[i] != null) ||
                (i< ret_objs.length &&  ret_objs[i] != null) )
              mmem.create_alias_active(i,ret_mem.at(i).above_center() ? cmem : rmem,null);
          mem = gvn.xform(mmem);
        }
        return inline(gvn, call, ret.ctl(), mem, ret.val(), null/*do not unwire, because using the entire function body inplace*/);
      }
    }

    // If the call's allowed functions excludes any wired, remove the extras
    BitSet bs = fidxs.tree().plus_kids(fidxs);
    if( !fidxs.test(BitsFun.ALL) ) {
      for( int i = 0; i < nwired(); i++ ) {
        RetNode ret = wired(i);
        if( !bs.get(ret.fidx()) ) { // Wired call is not actually executable?
          // Remove the edge.  Happens after e.g. cloning a function, where
          // both cloned and original versions are wired, but only one is
          // reachable.
          unwire(gvn,call,ret);
          del(wire_num(i--));
        }
      }
    }

    // If call allows many functions, bail out.
    int fidx = fidxs.abit();
    if( fidx == -1 || BitsFun.is_parent(fidx) )
      return null; // Multiple fidxs

    // Call allows 1 function not yet wired, sanity check it.
    FunNode fun = FunNode.find_fidx(fidx);
    if( fun.is_forward_ref() || fun.is_dead() ) return null;
    if( gvn.type(fun) == Type.XCTRL ) return null;

    // Arg counts must be compatible
    int cnargs = call.nargs();
    if( fun.nargs() != cnargs )
      return null;

    // Single choice; check no conversions needed
    TypeStruct formals = fun._tf._args;
    for( int i=1; i<cnargs; i++ ) { // Start at 1 to skip closure hidden arg
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
    if( (rmem instanceof ParmNode && rmem.in(0) == fun) || gvn.type(rmem)==TypeMem.EMPTY )
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

    // Wire.  During GCP, cannot call "xform" since e.g. types are not final
    // nor constant yet - and need to add all new nodes to the GCP worklist.
    // During iter(), must call xform() to register all new nodes.

    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        // See CallNode output tuple type for what these horrible magic numbers are.
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        Node actual = idx==-1 ? new ConNode<>(TypeRPC.make(call._rpc)) :
          (idx==-2 ? new MProjNode(call,2) : new ProjNode(call,idx+3));
        if( idx==0 )
          actual = new FP2ClosureNode(gvn.xform(actual));
        if( gvn._opt_mode == 2 ) {
          gvn.setype(actual,actual.all_type().startype());
          gvn.add_work(actual);
        }
        else actual = gvn.xform(actual);
        gvn.add_def(arg,actual);
      }
    }

    // Add matching control to function
    Node cproj = new CProjNode(call,0);
    cproj = gvn._opt_mode == 2 ? gvn.add_work(cproj) : gvn.xform(cproj);
    gvn.add_def(fun,cproj);
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
    CallNode call = is_copy() ? ((CallNode)in(3)) : call();
    Type ctl = gvn.type(call.ctl()); // Call is reached or not?
    if( ctl != Type.CTRL && ctl != Type.ALL )
      return TypeTuple.CALLE.dual();
    int cnargs = call.nargs();

    // Get Call result.  If the Call args are in-error, then the Call is called
    // and we flow types to the post-call.... BUT the bad args are NOT passed
    // along to the function being called.
    // tcall[0] = Control
    // tcall[1] = Full available memory
    // tcall[2] = Memory slice passed to function
    // tcall[3] = TypeFunPtr passed to FP2Closure
    // tcall[4+]= Arg types
    TypeTuple tcall = (TypeTuple)gvn.type(call);
    Type tfptr = tcall.at(3);
    if( !(tfptr instanceof TypeFunPtr) ) // Call does not know what it is calling?
      return TypeTuple.CALLE;
    TypeFunPtr funt = (TypeFunPtr)tfptr;
    BitsFun fidxs = funt.fidxs();
    if( fidxs.test(BitsFun.ALL) ) // All functions are possible?
      return fidxs.above_center() ? TypeTuple.CALLE.dual() : TypeTuple.CALLE;  // Worse-case result
    // If we fall from choice-functions to the empty set of called functions, freeze our output.
    // We might fall past empty and get a valid set.  Probably wrong; if we ever see a
    // choice set of functions, we should not execute.
    if( fidxs.is_empty() ) return gvn.self_type(this);

    // Merge returns from all fidxs, wired or not.  Required during GCP to keep
    // optimistic.  JOIN if above center, merge otherwise.  Wiring the calls
    // gives us a faster lookup, but need to be correct wired or not.

    // Gather the set of aliases passed into the function.
    //BitsAlias call_aliases = call_mem.aliases();
    // Set of all possible target functions
    Bits.Tree<BitsFun> tree = fidxs.tree();
    BitSet bs = tree.plus_kids(fidxs);
    // Lifting or dropping Unresolved calls
    boolean lifting = fidxs.above_center();
    Type t = lifting ? TypeTuple.RET : TypeTuple.XRET;
    for( int fidx = bs.nextSetBit(0); fidx >= 0; fidx = bs.nextSetBit(fidx+1) ) {
      if( tree.is_parent(fidx) ) continue;   // Will be covered by children
      FunNode fun = FunNode.find_fidx(fidx); // Lookup, even if not wired
      if( fun==null || fun.is_dead() )
        continue;              // Can be dead, if the news has not traveled yet
      RetNode ret = fun.ret();
      if( ret == null ) continue; // Can be dead, if the news has not traveled yet
      if( fun.nargs() != cnargs ) { // This call-path has wrong args, is in-error for this function
        // If lifting, we choose not to call this variant.
        if( lifting ) continue;
        // Cannot just ignore/continue because the remaining functions might
        // allow the call site to produce a constant and optimize away.
        else return TypeTuple.CALLE; // No good result until the input function is sensible
      }
      TypeTuple tret = (TypeTuple)gvn.type(ret); // Type of the return
      // TODO: Renable this.
      // Lift the returned memory to be no more than what is available at the
      // call entry plus the function closures - specifically not all the
      // memory from unrelated calls to this same function.
      //TypeMem ret_mem_untrimmed = ((TypeMem)tret.at(1));

      // Aliases from the function.  Includes aliases passed in from other call sites.
      //BitsAlias ret_aliases = ret_mem_untrimmed.aliases();
      //
      // Trim to aliases available from this call path.
      //BitsAlias call_trimmed = (BitsAlias)ret_aliases.join(call_aliases);
      //BitsAlias plus_local = call_trimmed.meet(fun._closure_aliases);
      //
      // Trim return memory to what is possible on this path.
      //TypeMem ret_mem_trimmed = ret_mem_untrimmed.trim_to_alias(plus_local);
      // Build a full return type.
      //TypeTuple tret2 = TypeTuple.make(tret.at(0),ret_mem_trimmed,tret.at(2));
      TypeTuple tret2 = tret;
      t = lifting ? t.join(tret2) : t.meet(tret2);

      // Make real from virtual CG edges in GCP/Opto by wiring calls.
      if( gvn._opt_mode==0 ) gvn.add_work(this); // Not during parsing, but check afterwards
      if( gvn._opt_mode!=0 &&        // Not during parsing
          !is_copy() &&              // Not if collapsing
          !fidxs.above_center() &&   // Still settling down to possibilities
          !fun.is_forward_ref() &&   // Call target is undefined
          tcall.at(0)==Type.CTRL )   // Call args are not in error
        wire(gvn,call,fun,ret);
    }
    // Meet the call-bypass aliases with the function aliases.  If the function
    // produces a new alias it might still have been called previously and thus
    // the call-bypass aliases might be modified elsewhere.... so despite a
    // function being the sole producing of an alias, we still have to MEET all
    // aliases.  If the caller contains none of an alias so that the function
    // precisely stomps all of it, the call needs to be reporting [1#:~obj] -
    // in which case a normal MEET suffices.
    TypeTuple tt = (TypeTuple)t;
    Type pre_c_mem = tcall.at(1);
    TypeMem pre_call_memory = pre_c_mem instanceof TypeMem
      ? (TypeMem)pre_c_mem
      : (pre_c_mem.above_center() ? TypeMem.XMEM : TypeMem.MEM);
    Type post_call_mem = tt.at(1).meet(pre_call_memory);
    // Return a FOUR-tuple: standard call (control,memory,value) return, plus
    // JUST the function return memories.  Loads and Stores can bypass the
    // function call, if the aliasing allows.
    return TypeTuple.make(tt.at(0),post_call_mem,tt.at(2),tt.at(1));
  }

  // Set of used aliases across all inputs (not StoreNode value, but yes address)
  @Override public BitsAlias alias_uses(GVNGCM gvn) {
    assert is_copy();
    return BitsAlias.NZERO; // Conservative do-nothing.  Since a copy, it will be removed shortly
  }

  // Inline the CallNode.  Remove all edges except the results.  This triggers
  // "is_copy()", which in turn will trigger the following ProjNodes to inline.
  private Node inline( GVNGCM gvn, CallNode call, Node ctl, Node mem, Node rez, RetNode ret ) {
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
    add_def(ctl.unhook());
    add_def(mem.unhook());
    add_def(rez.unhook());
    add_def(call.unhook());         // Hook call, to get FIDX for value filtering.
    return this;
  }

  private void unwire(GVNGCM gvn, CallNode call, RetNode ret) {
    if( ret.is_copy() ) return;
    FunNode fun = ret.fun();
    for( int i=1; i<fun._defs._len; i++ ) // Unwire
      if( fun.in(i).in(0)==call ) gvn.set_def_reg(fun,i,gvn.con(Type.XCTRL));
  }
  // If slot 0 is not a CallNode, we have been inlined.
  boolean is_copy() { return !(in(0) instanceof CallNode); }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return is_copy() ? in(idx) : null; }
  @Override public Type all_type() { return TypeTuple.CALLE; }
}
