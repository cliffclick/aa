package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import org.jetbrains.annotations.NotNull;

import java.util.BitSet;

// Call/apply node.
//
// Control is not required for an apply but inlining the function body will
// require it; slot 0 is for Control.  Slot 1 is function memory, slot 2 the
// function ptr - a Node typed as a TypeFunPtr; can be a FunPtrNode, an
// Unresolved, or e.g. a Phi or a Load.  Slots 3+ are for other args.
//
// When the function type simplifies to a single FIDX, the Call can inline.
//
// TFPs are actually Closures and include an extra argument for the enclosed
// environment (actually expanded out to one arg-per-used-scope).  These extra
// arguments are part of the function signature but are not direct inputs into
// the call.  FP2Closure strips out the FIDX and passes on just the display.
//
// The Call-graph is lazily discovered during GCP/opto.  Before then all
// functions are kept alive with a special control (see FunNode), and all Calls
// are assumed to call all functions... unless their fun() input is a trival
// function constant.
//
// As the Call-graph is discovered, Calls are "wired" to make it explicit: the
// Call control is wired to the FunNode/Region; call args are wired directly to
// function ParmNodes/PhiNode; the CallEpi is wired to the function RetNode.
// After GCP/opto the call-graph is explicit and fairly precise.  The call-site
// index is just like a ReturnPC value on a real machine; it dictates which of
// several possible returns apply... and can be merged like a PhiNode.
//
// Memory into   a Call is limited to call-reachable read-write memory.
// Memory out of a Call is limited to call-reachable writable   memory.
//
// ASCIIGram: Vertical   lines are part of the original graph.
//            Horizontal lines are lazily wired during GCP.
//
// TFP&Math
//  Memory: limited to reachable
//  |  |  arg0 arg1
//  |  \  |   /           Other Calls
//  |   | |  /             /  |  \
//  |   v v v             /   |   \
//  |    Call            /    |    \
//  |    C/M/Args       /     |     \
//  |      +--------->------>------->            Wired during GCP
//  |               FUN0   FUN1   FUN2
//  |               +--+   +--+   +--+
//  |               |  |   |  |   |  |
//  |               |  |   |  |   |  |
//  |               +--+   +--+   +--+
//  |          /-----Ret<---Ret<---Ret--\        Wired during GCP
//  |   CallEpi     fptr   fptr   fptr  Other
//  |    CProj         \    |    /       CallEpis
//  |    MProj          \   |   /
//  |    DProj           TFP&Math
//  \   / | \
//  MemMerge: limited to reachable writable
//
// Wiring a Call changes the Node graph and has to preserve invariants.  The
// graph has a major type invariant: at every moment in time computing the
// value() call on a Node (from the types of its inputs) produces a type which
// is monotonically better (either up or down, according to iter() vs gcp()).
//
// Wiring adds a bunch of edges and thus inputs.  The graph has to keep the
// type invariant after adding the edges, and this is not always possible; the
// types can flow to the Fun and the Call at a different rate, and the two
// not-connected Nodes might be out-of-type-order relative to each other.  The
// progress and monotonicity properties guarentee they will eventually align.
//
// Discovery of a CG edge happens when a Call's function value changes, but
// graph type alignment might be much later.  We want to act on the discovery
// of a CG edge now, but not flow types until they align.  See CallEpi for
// wired_not_typed bits.

public class CallNode extends Node {
  int _rpc;                 // Call-site return PC
  boolean _unpacked;        // Call site allows unpacking a tuple (once)
  boolean _is_copy;         // One-shot flag set when inlining an entire single-caller-single-called
  // Example: call(arg1,arg2)
  // _badargs[0] points to the opening paren.
  // _badargs[1] points to the start of arg1, same for arg2, etc.
  Parse[] _badargs;         // Errors for e.g. wrong arg counts or incompatible args; one error point per arg.
  public CallNode( boolean unpacked, Parse[] badargs, Node... defs ) {
    super(OP_CALL,defs);
    _rpc = BitsRPC.new_rpc(BitsRPC.ALL); // Unique call-site index
    _unpacked=unpacked;         // Arguments are typically packed into a tuple and need unpacking, but not always
    _badargs = badargs;
  }

  String xstr() { return ((is_dead() || is_copy()) ? "x" : "C")+"all#"+_rpc; } // Self short name
  String  str() { return xstr(); }       // Inline short name

  // Call arguments:
  // 0 - Control.  If XCTRL, call is not reached.
  // 1 - Memory.  This is memory into the call.
  // 2 - Function pointer, typed as a TypeFunPtr.  Might be a FunPtrNode, might
  //     be e.g. a Phi or a Load.  This is argument#0, both as the Closure AND
  //     as the Code pointer.  The output type here is trimmed to what is "resolved"
  // 3+  Other "normal" arguments, numbered#1 and up.

  // Number of actual arguments, including the closure/code ptr.
  // This is 2 higher than the user-visible arg count.
  int nargs() { return _defs._len-2; }
  // Actual arguments.  Arg(0) is allowed and refers to the Display/TFP.
  Node arg ( int x ) { assert x>=0; return _defs.at(x+2); }
  Node argm( int x ) { return x==-2 ? mem() : arg(x); }
  // Set an argument.  Use 'set_fun' to set the Display/Code.
  Node set_arg    (int idx, Node arg, GVNGCM gvn) { assert idx>0; return set_def(idx+2,arg,gvn); }

  public  Node ctl() { return in(0); }
  public  Node mem() { return in(1); }
  public  Node fun() { return in(2); }
  Node set_fun    (Node fun, GVNGCM gvn) { return set_def(2,fun,gvn); }
  public  void set_fun_reg(Node fun, GVNGCM gvn) { gvn.set_def_reg(this,2,fun); }
  public BitsFun fidxs(GVNGCM gvn) {
    Type tf = gvn.type(fun());
    return tf instanceof TypeFunPtr ? ((TypeFunPtr)tf).fidxs() : null;
  }

  // Add a bunch of utilities for breaking down a Call.value tuple:
  // takes a Type, upcasts to tuple, & slices by name.
  // ts[0] = Ctrl = in(0)
  // ts[1] = Mem into the caller = mem() = in(1)
  // ts[2] = Function pointer (code ptr + display) == in(2) == arg(0)
  // ts[3] = in(3) == arg(1)
  // ts[4]...

  static final int MEMIDX=1; // Memory into the caller
  static final int ARGIDX=2; //
  static        Type       tctl( Type tcall ) { return             ((TypeTuple)tcall).at(0); }
  static        TypeMem    tmem( Type tcall ) { return tmem(((TypeTuple)tcall)._ts); }
  static        TypeMem    tmem( Type[] ts  ) { return (TypeMem)ts[MEMIDX]; } // caller memory passed around function
  static public TypeFunPtr ttfp( Type tcall ) { return (TypeFunPtr)((TypeTuple)tcall).at(ARGIDX); }
  static TypeTuple set_ttfp( TypeTuple tcall, TypeFunPtr nfptr ) { return tcall.set(ARGIDX,nfptr); }
  static Type       targ( Type tcall, int x ) { return targ(((TypeTuple)tcall)._ts,x); }
  static Type       targ( Type[] ts, int x ) { return ts[ARGIDX+x]; }

  // Clones during inlining all become unique new call sites.  The original RPC
  // splits into 2, and the two new children RPCs replace it entirely.  The
  // original RPC may exist in the type system for a little while, until the
  // children propagate everywhere.
  @Override @NotNull CallNode copy( boolean copy_edges, GVNGCM gvn) {
    CallNode call = (CallNode)super.copy(copy_edges,gvn);
    ConNode old_rpc = gvn.con(TypeRPC.make(_rpc));
    call._rpc = BitsRPC.new_rpc(_rpc); // Children RPC
    Type oldt = gvn.unreg(this);       // Changes hash, so must remove from hash table
    _rpc = BitsRPC.new_rpc(_rpc);      // New child RPC for 'this' as well.
    gvn.rereg(this,oldt);              // Back on list
    // Swap out the existing old rpc users for the new.
    // Might be no users of either.
    ConNode new_rpc = gvn.con(TypeRPC.make(_rpc));
    gvn.add_work(gvn.subsume(old_rpc,new_rpc));
    return call;
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;
    Type tc = gvn.type(this);
    if( !(tc instanceof TypeTuple) ) return null;
    TypeTuple tcall = (TypeTuple)tc;
    // Dead, do nothing
    if( gvn.type(ctl())!=Type.CTRL ) {     // Dead control (NOT dead self-type, which happens if we do not resolve)
      if( (ctl() instanceof ConNode) ) return null;
      // Kill all inputs with type-safe dead constants
      set_def(1,gvn.con(TypeMem.XMEM),gvn);
      set_def(2,gvn.con(TypeFunPtr.GENERIC_FUNPTR.dual()),gvn);
      if( is_dead() ) return this;
      for( int i=3; i<_defs._len; i++ )
        set_def(i,gvn.con(Type.XSCALAR),gvn);
      gvn.add_work_defs(this);
      return set_def(0,gvn.add_work(gvn.con(Type.XCTRL)),gvn);
    }

    // When do I do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) {          // Not yet unpacked a tuple
      assert nargs()==2;        // The return, Display plus the arg tuple
      Node mem = mem();
      Node arg1 = arg(1);
      Type tadr = gvn.type(arg1);
      // Bypass a merge on the 2-arg input during unpacking
      if( tadr instanceof TypeMemPtr && mem instanceof MemMergeNode ) {
        int alias = ((TypeMemPtr)tadr)._aliases.abit();
        if( alias == -1 ) throw AA.unimpl(); // Handle multiple aliases, handle all/empty
        Node obj = ((MemMergeNode)mem).alias2node(alias);
        if( obj instanceof OProjNode && arg1 instanceof ProjNode && arg1.in(0) instanceof NewNode ) {
          NewNode nnn = (NewNode)arg1.in(0);
          remove(_defs._len-1,gvn); // Pop off the NewNode tuple
          int len = nnn._defs._len;
          for( int i=2; i<len; i++ ) // Push the args; unpacks the tuple
            add_def( nnn.in(i));
          _unpacked = true;     // Only do it once
          return this;
        }
      }
    }
    // Have some sane function choices?
    TypeFunPtr tfp  = ttfp(tcall);
    BitsFun fidxs = tfp.fidxs();
    if( fidxs==BitsFun.EMPTY ) // TODO: zap function to empty function constant
      return null;             // Zero choices

    // If we have a single function allowed, force the function constant.
    Node unk = fun();           // Function epilog/function pointer
    int fidx = fidxs.abit();    // Check for single target
    if( fidx != -1 && !(unk instanceof FunPtrNode) )
      return set_fun(FunNode.find_fidx(Math.abs(fidx)).ret().funptr(),gvn);

    // If the function is unresolved, see if we can resolve it now.
    // Fidxs are typically low during iter, but can be high during
    // iter post-GCP on error calls where nothing resolves.
    if( unk instanceof UnresolvedNode && !fidxs.above_center() && !fidxs.test(1)) {
      BitsFun rfidxs = resolve(fidxs,tcall._ts,gvn._opt_mode==2);
      if( rfidxs==null ) return null;            // Dead function, stall for time
      FunPtrNode fptr = least_cost(gvn, rfidxs); // Check for least-cost target
      if( fptr != null ) return set_fun(fptr, gvn); // Resolve to 1 choice
    }

    // Wire valid targets.
    CallEpiNode cepi = cepi();
    if( cepi!=null && cepi.check_and_wire(gvn) )
      return this;              // Some wiring happened

    // Check for dead args and trim; must be after all wiring is done because
    // unknown call targets can appear during GCP and use the args.  After GCP,
    // still must verify all called functions have the arg as dead, because
    // alive args still need to resolve.  Constants are an issue, because they
    // fold into the Parm and the Call can lose the matching DProj while the
    // arg is still alive.
    if( gvn._opt_mode > 2 && err(gvn,true)==null ) {
      Node progress = null;
      for( int i=1; i<nargs(); i++ ) // Skip the FP/DISPLAY arg, as its useful for error messages
        if( ProjNode.proj(this,i+ARGIDX)==null &&
            !(arg(i) instanceof ConNode && gvn.type(arg(i))==Type.XSCALAR) ) // Not already folded
          progress = set_arg(i,gvn.con(Type.XSCALAR),gvn); // Kill dead arg
      if( progress != null ) return this;
    }

    return null;
  }

  // Pass thru all inputs directly - just a direct gather/scatter.  The gather
  // enforces SESE which in turn allows more precise memory and aliasing.  The
  // full scatter lets users decide the meaning; e.g. wired FunNodes will take
  // the full arg set but if the call is not reachable the FunNode will not
  // merge from that path.  Result tuple type:
  @Override public Type value(GVNGCM gvn) {
    if( _is_copy ) return gvn.self_type(this);

    // Pinch to XCTRL/CTRL
    Type ctl = gvn.type(ctl());
    if( !_is_copy && gvn._opt_mode>0 && cepi()==null ) ctl = Type.XCTRL; // Dead from below
    if( ctl != Type.CTRL ) return ctl.oob();
    final Type[] ts = TypeAry.get(_defs._len+(ARGIDX-2));
    ts[0] = Type.CTRL;

    // Not a memory to the call?
    Type mem = gvn.type(mem());
    if( !(mem instanceof TypeMem) ) return mem.oob();
    TypeMem tmem = (TypeMem)(ts[MEMIDX]=mem); // Memory into the caller, not callee

    // Copy args for called functions.  Arg0 is display, handled below.
    for( int i=0; i<nargs(); i++ )
      ts[i+ARGIDX] = gvn.type(arg(i));

    // Not a function to call?
    Type tfx = gvn.type(fun());
    if( !(tfx instanceof TypeFunPtr) )
      tfx = tfx.above_center() ? TypeFunPtr.GENERIC_FUNPTR.dual() : TypeFunPtr.GENERIC_FUNPTR;
    TypeFunPtr tfp = (TypeFunPtr)tfx;
    BitsFun fidxs = tfp.fidxs();
    if( !fidxs.is_empty() && fidxs.above_center()!=tfp._disp.above_center() )
      return gvn.self_type(this); // Display and FIDX mis-aligned; stall
    // Resolve; only keep choices with sane arguments during GCP
    BitsFun rfidxs = resolve(fidxs,ts,gvn._opt_mode==2);
    if( rfidxs==null ) return gvn.self_type(this); // Dead function input, stall until this dies
    // Call.ts[2] is a TFP just for the resolved fidxs and display.
    ts[ARGIDX] = TypeFunPtr.make(rfidxs,tfp._nargs,rfidxs.above_center() == fidxs.above_center() ? tfp._disp : tfp._disp.dual());

    return TypeTuple.make(ts);
  }

  // Compute live across uses.  If pre-GCP, then we may not be wired and thus
  // have not seen all possible function-body uses.  Check for #FIDXs == nwired().
  @Override public TypeMem live( GVNGCM gvn) {
    if( gvn._opt_mode < 2 ) {
      BitsFun fidxs = fidxs(gvn);
      if( fidxs == null ) return TypeMem.ALLMEM; // Assume Something Good will yet happen
      if( fidxs.above_center() ) return _live; // Got choices, dunno which one will stick
      CallEpiNode cepi = cepi();
      if( cepi==null ) return _live; // Collapsing
      if( gvn.type(ctl()) == Type.XCTRL ) return _live; // Unreachable
      // Expand (actually fail) if any parents
      BitSet bs = fidxs.tree().plus_kids(fidxs);
      if( bs.cardinality() > cepi.nwired() ) // More things to call
        return _live; // Cannot improve
    }
    // All choices discovered during GCP.  If the call is in-error it may not
    // resolve and so will have no uses other than the CallEpi - which is good
    // enough to declare this live, so it exists for errors.
    return super.live(gvn);
  }
  @Override public boolean basic_liveness() { return false; }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( is_copy() ) {           // Target is as alive as our projs are.
      int idx = _defs.find(def);
      ProjNode proj = ProjNode.proj(this,idx);
      if( proj != null ) return proj._live;
      if( idx==1 ) return _live; // Memory
      return def.basic_liveness() ? TypeMem.ALIVE : TypeMem.ANYMEM; // Args always alive
    }
    if( def==fun() ) {                               // Function argument
      if( gvn._opt_mode < 2 ) return TypeMem.ALLMEM; // Prior to GCP, assume all fptrs are alive
      if( !(def instanceof FunPtrNode) ) return _live;
      int dfidx = ((FunPtrNode)def).ret()._fidx;
      return live_use_call(gvn,dfidx); // Can be precise
    }
    if( def!=mem() )            // Some argument
      return def.basic_liveness() ? TypeMem.ESCAPE : TypeMem.ANYMEM;    // Args always alive and escape
    // Needed to sharpen args for e.g. resolve and errors.
    Type tcall = gvn.type(this);
    if( tcall==Type.ANY ) return _live; // No type to sharpen
    BitsAlias aliases = BitsAlias.EMPTY;
    for( int i=1; i<nargs(); i++ ) {
      Type targ = targ(tcall,i);
      if( TypeMemPtr.OOP.isa(targ) )
        { aliases=BitsAlias.FULL; break; }; // All possible pointers, so all memory is alive
      if( !(targ instanceof TypeMemPtr) ) continue; // Not a pointer, does not need memory to sharpen
      if( targ.above_center() ) continue; // Have infinite choices still, no memory
      aliases = aliases.meet(((TypeMemPtr)targ)._aliases);
    }
    // Conservative too strong; need only memories that go as deep as the
    // formal types.
    TypeMem tmem = tmem(tcall);
    TypeMem tmem2 = tmem.slice_all_aliases_plus_children(aliases);
    TypeMem tmem3 = (TypeMem)tmem2.meet(_live);
    return tmem3;
  }

  TypeMem live_use_call( GVNGCM gvn, int dfidx ) {
    Type tcall = gvn.type(this);
    if( !(tcall instanceof TypeTuple) ) return tcall.above_center() ? TypeMem.DEAD : _live;
    TypeFunPtr tfp = ttfp(tcall);
    // If resolve has chosen this dfidx, then the FunPtr is alive.
    BitsFun fidxs = tfp.fidxs();
    return !fidxs.above_center() && fidxs.test_recur(dfidx) ? TypeMem.ALIVE : TypeMem.DEAD;
  }


  // Resolve an Unresolved.  Called in value() and so must be monotonic.
  // Strictly looks at arguments and the list of function choices.  Mostly all
  // arguments start in GCP & Iter at the extremes and move towards the center
  // and resolve() cannot move off the extreme until ALL args move.
  // See TestNodeSmall.java for the large mapping table test.
  //
  // Rules "cookbook" to help map the table:
  // - Some args High & no Low, keep all & join (ignore Good,Bad)
  // - Some args Low & no High, keep all & meet (ignore Good,Bad)
  // - Mix High/Low & no Good , keep all
  // - Some Good, no Low, no High, drop Bad & fidx?join:meet
  // - All Bad, like Low: keep all & meet
  // At any time during iter (not GCP), an arg can go dead and
  // be removed - so losing an arg can only lift.
  private static final int BAD=1, GOOD=2, LOW=4, HIGH=8, DEAD=16;

  BitsFun resolve( BitsFun fidxs, Type[] targs, boolean gcp ) {
    if( fidxs==BitsFun.EMPTY) return fidxs; // Nothing to resolve
    if( fidxs==BitsFun.ANY  ) return fidxs; // No point in attempting to resolve all things
    if( fidxs==BitsFun.FULL ) return fidxs; // No point in attempting to resolve all things

    int flags = 0;
    for( int fidx : fidxs )
      // Parent/kids happen during inlining
      for( int kidx=fidx; kidx!=0; kidx=BitsFun.next_kid(fidx,kidx) )
        flags |= resolve(kidx,targs,gcp);
    if( x(flags,DEAD) ) return null; // Caller should stall for time, till dead folds up
    // - Some args High & no Low, keep all & join (ignore Good,Bad)
    if(  x(flags,HIGH) && !x(flags,LOW) ) return sgn(fidxs,true);
    // - Some args Low & no High, keep all & meet (ignore Good,Bad)
    if( !x(flags,HIGH) &&  x(flags,LOW) ) return sgn(fidxs,false);
    // - Mix High/Low, keep all & fidx (ignore Good,Bad)
    if(  x(flags,HIGH) &&  x(flags,LOW) ) return fidxs;
    // - All Bad, like Low: keep all & meet.  Bad args can go dead, effectively lifting.
    if( !x(flags,HIGH) && !x(flags,LOW) && !x(flags,GOOD) && flags!=0 )
      return sgn(fidxs,false);
    // No args is at least as high as anything with args
    if( flags==0 )
      return sgn(fidxs,true);

    // Only had a single target coming in.
    if( fidxs.abit() != -1 ) // Single target
      // If BAD args can die (false in primitives, and false in UnresolvedNodes
      // where the BAD arg is required to make the signature unambiguous) then
      // return all the fidxs, and wait for some arg to die (or else the
      // program is in-error).
      return fidxs;

    // All that is left is the no-args case (all formals ignoring), no high/low
    // and some good and maybe bad.  Toss out the bad & return the remaining
    // fidxs with the same sign.
    BitsFun choices = BitsFun.EMPTY;
    for( int fidx : fidxs )
      // Parent/kids happen during inlining
      for( int kidx=fidx; kidx!=0; kidx=BitsFun.next_kid(fidx,kidx) )
        if( !BitsFun.is_parent(kidx) && !x(resolve(kidx,targs,gcp),BAD) )
          choices = choices.set(kidx);
    if( choices.abit() != -1 )  // Single choice with all good, no high, no low, no bad
      return choices;           // Report it low
    return sgn(choices,fidxs.above_center());
  }

  private static boolean x(int flags, int flag)  { return (flags&flag)==flag; }
  private static BitsFun sgn(BitsFun fidxs, boolean hi) {
    return fidxs.above_center()==hi ? fidxs : fidxs.dual();
  }

  // Return 4 bools as 4 bits based on whether or not the actual args meets the
  // formals: [High,Low,Good,Bad].  High > formal.dual >= Good >= formal > Low.
  // Bad is none of the prior (actual is neither above nor below the formal).
  int resolve( int fidx, Type[] targs, boolean gcp ) {
    if( BitsFun.is_parent(fidx) )
      return 0; // Parent is never a real choice.  See these during inlining.

    TypeMem tpre = tmem(targs); // Caller Memory (not Callee)
    FunNode fun = FunNode.find_fidx(fidx);
    if( fun==null || fun.is_dead() ) return DEAD; // Stale fidx leading to dead fun
    // Forward refs are only during parsing; assume they fit the bill
    if( fun.is_forward_ref() ) return LOW;   // Assume they work
    if( fun.nargs() != nargs() ) return BAD; // Wrong arg count, toss out
    // Toss out single-path (inlines specific to a single call-site) FunNodes
    // to the wrong call.  Happens because the parent fidx splits, and both
    // children appear at all call sites - for a little while.
    if( !fun.has_unknown_callers() && !is_copy() && !gcp ) {
      CallEpiNode cepi = cepi();
      if( cepi != null ) {
        int i; for( i=0; i<cepi.nwired(); i++ ) {
          RetNode ret = cepi.wired(i);
          if( !ret.is_copy() && ret.fun()==fun )
            break;
        }
        if( i==cepi.nwired() ) return 0; // While a (stale) fidx might be available, this path is for another call.
      }
    }
    TypeStruct formals = fun._sig._formals;  // Type of each argument
    int flags=0;
    for( int j=0; j<nargs(); j++ ) {
      Type formal = formals.at(j);
      if( fun.parm(j)==null ) continue;     // Arg is ignored
      Type actual = targ(targs,j);          // Calls skip ctrl & mem
      if( j==0 && actual instanceof TypeFunPtr )
        actual = ((TypeFunPtr)actual)._disp; // Extract Display type from TFP
      assert actual==actual.simple_ptr();    // Only simple ptrs from nodes
      actual = tpre.sharptr(actual); // Sharpen actual pointers before checking vs formals

      if( actual==formal ) { flags|=GOOD; continue; } // Arg is fine.  Covers NO_DISP which can be a high formal.
      Type mt_lo = actual.meet(formal       );
      Type mt_hi = actual.meet(formal.dual());
      if( mt_lo==actual ) flags|=LOW;       // Low
      else if( mt_hi==actual ) flags|=GOOD; // Good
      else if( mt_hi==formal.dual() ) flags|=HIGH;
      else if( mt_lo==formal ) flags|=GOOD; // handles some display cases with prims hi/lo inverted
      else flags|=BAD;                      // Side-ways is bad
    }
    if( flags==0 ) flags=GOOD; // No args counts as all-good-args
    return flags;
  }


  // Amongst these choices return the least-cost.  Some or all might be
  // invalid.
  public FunPtrNode least_cost(GVNGCM gvn, BitsFun choices) {
    if( choices==BitsFun.EMPTY ) return null;
    assert choices.bitCount() > 0; // Must be some choices
    assert choices.above_center() == (gvn._opt_mode==2);
    int best_cvts=99999;           // Too expensive
    FunPtrNode best_fptr=null;     //
    TypeStruct best_formals=null;  //
    boolean tied=false;            // Ties not allowed
    for( int fidx : choices ) {
      // Parent/kids happen during inlining
      for( int kidx=fidx; kidx!=0; kidx=BitsFun.next_kid(fidx,kidx) ) {
        if( BitsFun.is_parent(kidx) )
          continue;

        FunNode fun = FunNode.find_fidx(kidx);
        if( fun.nargs()!=nargs() || fun.ret() == null ) continue; // BAD/dead
        TypeStruct formals = fun._sig._formals; // Type of each argument
        int cvts=0;                        // Arg conversion cost
        for( int j=1; j<nargs(); j++ ) {   // Skip arg#0, the display
          if( fun.parm(j)==null ) continue; // Formal is ignored
          Type actual = gvn.type(arg(j));
          Type formal = formals.at(j);
          if( actual==formal ) continue;
          byte cvt = actual.isBitShape(formal); // +1 needs convert, 0 no-cost convert, -1 unknown, 99 never
          if( cvt == -1 ) return null; // Might be the best choice, or only choice, dunno
          cvts += cvt;
        }

        if( cvts < best_cvts ) {
          best_cvts = cvts;
          best_fptr = fun.ret().funptr();
          best_formals = formals;
          tied=false;
        } else if( cvts==best_cvts ) {
          // Look for monotonic formals
          int fcnt=0, bcnt=0;
          for( int i=0; i<formals._ts.length; i++ ) {
            Type ff = formals.at(i), bf = best_formals.at(i);
            if( ff==bf ) continue;
            Type mt = ff.meet(bf);
            if( ff==mt ) bcnt++;       // Best formal is higher than new
            else if( bf==mt ) fcnt++;  // New  formal is higher than best
            else { fcnt=bcnt=-1; break; } // Not monotonic, no obvious winner
          }
          // If one is monotonically higher than the other, take it
          if( fcnt > 0 && bcnt==0 ) { best_fptr = fun.ret().funptr(); best_formals = formals; }
          else if( fcnt==0 && bcnt > 0 ) {} // Keep current
          else tied=true;                   // Tied, ambiguous
        }
      }
    }
    if( best_cvts >= 99 ) return null; // No valid functions
    return tied ? null : best_fptr; // Ties need to have the ambiguity broken another way
  }

  @Override public String err(GVNGCM gvn) { return err(gvn,false); }
  String err(GVNGCM gvn, boolean fast) {
    // Fail for passed-in unknown references directly.
    for( int j=1; j<nargs(); j++ )
      if( arg(j).is_forward_ref() )
        return fast ? "" : _badargs[j].forward_ref_err( FunNode.find_fidx(((FunPtrNode)arg(j)).ret()._fidx) );

    // Expect a function pointer
    Type tfun = gvn.type(fun());
    if( !(tfun instanceof TypeFunPtr) )
      return fast ? "" : _badargs[0].errMsg("A function is being called, but "+tfun+" is not a function type");
    TypeFunPtr tfp = (TypeFunPtr)tfun;

    // Indirectly, forward-ref for function type
    if( tfp.is_forward_ref() ) // Forward ref on incoming function
      return _badargs[0].forward_ref_err(FunNode.find_fidx(tfp.fidx()));

    // bad-arg-count
    if( tfp._nargs != nargs() )
      return fast ? "" : _badargs[0].errMsg("Passing "+(nargs()-1)+" arguments to "+tfp.names(false)+" which takes "+(tfp._nargs-1)+" arguments");

    // Call did not resolve
    BitsFun fidxs = tfp.fidxs();
    if( fidxs.is_empty() || fidxs.above_center() ) // This is an unresolved call
      return fast ? "" : _badargs[0].errMsg("Unable to resolve call");

    // If ANY args are ANY they will fail the arg check, BUT will be reported
    // first where they became an ANY.
    if( !fast )
      for( int j=1; j<nargs(); j++ ) {
        Type ta = gvn.type(arg(j));
        if( ta==Type.ANY || ta==Type.ALL )
          return null;
      }

    // Now do an arg-check.
    for( int j=1; j<nargs(); j++ ) {
      Type actual = gvn.sharptr(arg(j),mem());
      Ary<Type> ts=null;
      for( int fidx : tfp._fidxs ) {
        FunNode fun = FunNode.find_fidx(fidx);
        if( fun.is_dead() ) return "";
        TypeStruct formals = fun._sig._formals; // Type of each argument
        if( fun.parm(j)==null ) continue;  // Formal is dead
        Type formal = formals.at(j);
        if( actual.isa(formal) ) continue; // Actual is a formal
        if( fast ) return "";              // Fail-fast
        if( ts==null ) ts = new Ary<>(new Type[1],0);
        if( ts.find(formal) == -1 ) // Dup filter
          ts.push(formal);          // Add broken type
      }
      if( ts!=null )
        return _badargs[j].typerr(actual,mem(),ts.asAry());
    }

    return null;
  }

  public CallEpiNode cepi() {
    for( Node cepi : _uses )    // Find CallEpi for bypass aliases
      if( cepi instanceof CallEpiNode )
        return (CallEpiNode)cepi;
    return null;
  }
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }
  boolean is_copy() { return _is_copy; }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    return _is_copy ? in(idx<=(ARGIDX-2) ? idx : idx-(ARGIDX-2)) : null;
  }
  @Override Node is_pure_call() { return fun().is_pure_call()==null ? null : mem(); }
}
