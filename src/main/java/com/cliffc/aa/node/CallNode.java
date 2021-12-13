package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.Env.GVN;

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
// progress and monotonicity properties guarantee they will eventually align.
//
// Discovery of a CG edge happens when a Call's function value changes, but
// graph type alignment might be much later.  We want to act on the discovery
// of a CG edge now, but not flow types until they align.  See CallEpi for
// wired_not_typed bits.

public class CallNode extends Node {
  int _rpc;                 // Call-site return PC
  boolean _unpacked;        // One-shot flag; call site allows unpacking a tuple
  boolean _is_copy;         // One-shot flag; Call will collapse
  public boolean _not_resolved_by_gcp; // One-shot flag set when GCP cannot resolve; this Call is definitely in-error
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

  @Override public String xstr() { return (_is_copy ? "CopyCall" : (is_dead() ? "Xall" : "Call"))+(_not_resolved_by_gcp?"_UNRESOLVED":""); } // Self short name
  String  str() { return xstr(); }       // Inline short name
  @Override public boolean is_mem() {    // Some calls are known to not write memory
    CallEpiNode cepi = cepi();
    return cepi!=null && ProjNode.proj(cepi,MEM_IDX)!=null;
  }

  // Call arguments:
  // 0 - Control.  If XCTRL, call is not reached.
  // 1 - Memory.  This is memory into the call and also arg#0
  // 2 - Function.  A TypeFunPtr; includes the display type.
  // 3+  Other "normal" arguments, numbered#ARG_IDX and up.
  //     The output type here is trimmed to what is "resolved"
  public  Node ctl() { return in(CTL_IDX); }
  public  Node mem() { return in(MEM_IDX); }
  public  Node fdx() { return in(DSP_IDX); } // Function and display

  // Number of actual arguments, including closure/display at DSP_IDX.
  int nargs() { return _defs._len; }
  // Actual arguments.  Arg(1) is allowed and refers to memory; arg(2) to the Display/TFP.
  Node arg ( int x ) { assert x>=0; return _defs.at(x); }
  // Set an argument.  Use 'set_fun' to set the Code.
  Node set_arg (int idx, Node arg) { assert idx>=DSP_IDX && idx <nargs(); return set_def(idx,arg); }
  public Node set_fdx( Node fun) { return set_def(DSP_IDX, fun);}
  public void set_mem( Node mem) { set_def(MEM_IDX, mem); }

  // Add a bunch of utilities for breaking down a Call.value tuple:
  // takes a Type, upcasts to tuple, & slices by name.
  // ts[0] == in(0) == ctl() == Ctrl
  // ts[1] == in(1) == mem() == Mem into the callee = mem()
  // ts[2] == in(2) == dsp() == Display pointer
  // ts[3] == in(3) == arg(3)
  // ts[4] == in(4) == arg(4)
  // ....
  // ts[_defs._len]   = Function, as a TFP
  // ts[_defs._len+1] = Escape-in aliases as a TMP
  static        Type       tctl( Type tcall ) { return             ((TypeTuple)tcall).at(CTL_IDX); }
  static        TypeMem    emem( Type tcall ) { return emem(       ((TypeTuple)tcall)._ts ); }
  static        TypeMem    emem( Type[] ts  ) { return (TypeMem   ) ts[MEM_IDX]; } // callee memory passed into function
  static        TypeMemPtr tesc( Type tcall ) {
    //if( !(tcall instanceof TypeTuple) ) return tcall.oob(TypeMemPtr.OOP);
    //TypeTuple tt = (TypeTuple)tcall;
    //return (TypeMemPtr)tt.at(tt.len()-1);
    throw unimpl();
  }
  // No-check must-be-correct get TFP
  static public TypeFunPtr ttfp( Type t ) {
    if( !(t instanceof TypeTuple) ) return (TypeFunPtr)t.oob(TypeFunPtr.GENERIC_FUNPTR);
    TypeTuple tcall = (TypeTuple)t;
    return (TypeFunPtr)tcall.at(tcall.len()-1/*-1 tescs turned off*/);
  }
  static TypeTuple set_ttfp( TypeTuple tcall, TypeFunPtr nfptr ) { return tcall.set(tcall.len()-1/*-1 tescs turned off*/,nfptr); }
  static Type targ( Type tcall, int x ) { return targ(((TypeTuple)tcall)._ts,x); }
  static Type targ( Type[] ts, int x ) { return ts[x]; }

  // Clones during inlining all become unique new call sites.  The original RPC
  // splits into 2, and the two new children RPCs replace it entirely.  The
  // original RPC may exist in the type system for a little while, until the
  // children propagate everywhere.
  @Override @NotNull public CallNode copy( boolean copy_edges) {
    CallNode call = (CallNode)super.copy(copy_edges);
    Node old_rpc = Node.con(TypeRPC.make(_rpc));
    call._rpc = BitsRPC.new_rpc(_rpc); // Children RPC
    set_rpc(BitsRPC.new_rpc(_rpc)); // New child RPC for 'this' as well.
    // Swap out the existing old rpc users for the new.
    // Might be no users of either.
    if( old_rpc._uses._len==0 ) old_rpc.kill();
    else old_rpc.subsume(Node.con(TypeRPC.make(_rpc)));
    return call;
  }

  @Override public Node ideal_reduce() {
    Node cc = in(0).is_copy(0);
    if( cc!=null ) return set_def(0,cc);
    // When do I do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) {          // Not yet unpacked a tuple
      assert nargs()==ARG_IDX+1;// Memory, Display plus the arg tuple
      Node arg = arg(ARG_IDX);
      Type tadr = arg._val;
      if( tadr instanceof TypeMemPtr && arg instanceof ProjNode ) {
        int alias = ((TypeMemPtr)tadr)._aliases.abit();
        if( alias == -1 ) throw unimpl(); // Handle multiple aliases, handle all/empty
        Node mem = mem();
        if( mem instanceof FreshNode ) mem = ((FreshNode)mem).id();
        // Bypass a MemJoin
        if( mem instanceof MemJoinNode ) {
          int jdx = ((MemJoinNode)mem).msp().find_alias_index(alias);
          if( jdx!=0 ) mem = mem.in(jdx);
        }
        // Find a tuple being passed in directly; unpack
        if( mem instanceof MrgProjNode && mem.in(0)==arg.in(0) ) {
          NewNode nnn = (NewNode)arg.in(0);
          pop(); // Pop off the NewNode tuple
          for( int i=ARG_IDX; i<nnn._defs._len; i++ ) // Push the args; unpacks the tuple
            add_def(nnn.in(i));
          _unpacked = true;     // Only do it once
          xval(); // Recompute value, this is not monotonic since replacing tuple with args
          GVN.add_work_new(this);// Revisit after unpacking
          return this;
        }
      }
    }

    Type tc = _val;
    if( !(tc instanceof TypeTuple) ) return null;
    TypeTuple tcall = (TypeTuple)tc;

    // Dead, do nothing
    if( tctl(tcall)!=Type.CTRL ) { // Dead control (NOT dead self-type, which happens if we do not resolve)
      if( (ctl() instanceof ConNode) ) return null;
      // Kill all inputs with type-safe dead constants
      set_mem(Node.con(TypeMem.XMEM));
      //set_dsp(Node.con(TypeFunPtr.GENERIC_FUNPTR.dual()));
      //if( is_dead() ) return this;
      //for( int i=ARG_IDX; i<_defs._len; i++ )
      //  set_def(i,Env.ANY);
      //gvn.add_work_defs(this);
      //return set_def(0,Env.XCTRL,gvn);
      throw unimpl();
    }

    // Have some sane function choices?
    TypeFunPtr tfp  = ttfp(tcall);
    BitsFun fidxs = tfp.fidxs();
    if( fidxs==BitsFun.EMPTY ) // TODO: zap function to empty function constant
      return null;             // Zero choices

    // Try to resolve to single-target
    if( fdx() instanceof UnresolvedNode ) {
      FunPtrNode fptr = ((UnresolvedNode)fdx()).resolve_value(((TypeTuple)_val)._ts);
      throw unimpl();
    }

    // Wire valid targets.
    CallEpiNode cepi = cepi();
    if( cepi!=null && cepi.check_and_wire(false) )
      return this;              // Some wiring happened

    // Check for dead args and trim; must be after all wiring is done because
    // unknown call targets can appear during GCP and use the args.  After GCP,
    // still must verify all called functions have the arg as dead, because
    // alive args still need to resolve.  Constants are an issue, because they
    // fold into the Parm and the Call can lose the matching DProj while the
    // arg is still alive.
    if( !is_keep() && err(true)==null ) {
      Node progress = null;
      for( int i=ARG_IDX; i<nargs(); i++ )
        if( ProjNode.proj(this,i)==null &&
            !(arg(i) instanceof ConNode) ) // Not already folded
          progress = set_arg(i,Env.ANY);   // Kill dead arg
      if( progress != null ) return this;
    }
    return null;
  }
  // Call reduces, then check the CEPI for reducing
  @Override public void add_reduce_extra() {
    Node cepi = cepi();
    if( !_is_copy && cepi!=null )
      Env.GVN.add_reduce(cepi);
    if( mem() instanceof MrgProjNode )
      Env.GVN.add_reduce(this);
    Env.GVN.add_flow(mem()); // Dead pointer args reduced to ANY, so mem() liveness lifts
  }

  @Override public Node ideal_grow() {
    // Check for a prior New and move past the call (pushes a store-like
    // behavior down).  The New address must not be reachable from the Call
    // arguments transitively, which is detected in the escape-in set.

    // Inserting a MemSplit is a ideal_grow, and swap_new could be an
    // ideal_mono, but they both use the same large correctness tests, so both
    // go under ideal_grow to avoid recomputing the test.
    Node mem = mem();
    CallEpiNode cepi = cepi();
    if( cepi==null || !(mem._val instanceof TypeMem) ) return null;
    ProjNode cepim = ProjNode.proj(cepi,MEM_IDX); // Memory projection from CEPI
    ProjNode cepid = ProjNode.proj(cepi,REZ_IDX); // Return projection from CEPI
    if( cepim == null ) return null;
    if( !(cepim._val instanceof TypeMem) ) return null;
    TypeMem tmcepi = (TypeMem) cepim._val;
    if( !mem._val.isa(tmcepi) ) return null; // Call entry stale relative to exit
    //BitsAlias escs = escapees();
    //// Check for prior      MrgProj/New
    //if( mem instanceof MrgProjNode )
    //  return _ideal_grow((MrgProjNode)mem,cepim,cepid,escs,-1);
    //// Check for prior Join/MrgProj/New
    if( mem instanceof MemJoinNode ) {
      if( !mem.check_solo_mem_writer(this) )
        return null;
      for( int i=1; i<mem._defs._len; i++ )
        if( mem.in(i) instanceof MrgProjNode ) {
          //Node x = _ideal_grow((MrgProjNode)mem.in(i),cepim,cepid,escs,i);
          //if( x!=null ) return x;
          throw unimpl();
        }
    }
    return null;
  }

  // Check for a Call/New that can either bypass or be placed in parallel
  private Node _ideal_grow(MrgProjNode mem, ProjNode cepim, ProjNode cepid, BitsAlias escs, int i) {
    // No alias overlaps
    int alias = mem.nnn()._alias;
    if( escs.test_recur(alias) ) return null;
    // No other readers or writers.  Expect the Call (or Join) and optionally DEFMEM
    if( mem._uses._len>2 ) return null;
    //if( mem._uses._len==2 && mem._uses.find(Env.DEFMEM)==-1 ) return null; // Something other than DEFMEM
    //
    //// If call returns same as new (via recursion), cannot split, but CAN swap.
    //TypeMem tmcepi = (TypeMem) cepim._val;
    //BitsAlias esc_out = CallEpiNode.esc_out(tmcepi,cepid==null ? Type.XNIL : cepid._val);
    //BitsAlias escs2 = escs.meet(esc_out);
    //Node jn = mem();
    //if( !escs2.is_empty() && !esc_out.test_recur(alias) ) { // No return conflict, so parallelize memory
    //  if( jn==mem )             // Bare Call/New; add a Split/Join.
    //    return MemSplitNode.insert_split(cepim,escs2,this,mem,mem);
    //  return null; // TODO: allow Call to move into existing JOIN
    //} else {                    // Else move New below Call.
    //  if( jn!=mem ) {           // Move New below Join
    //    Node pre = mem.mem();
    //    jn.set_def(i,pre);
    //    mem.set_def(MEM_IDX,jn);
    //    set_mem(mem);
    //    Env.GVN.add_unuse(jn);
    //    Env.GVN.add_unuse(mem);
    //  }
    //  return swap_new(cepim,mem); // Move New below Call
    //}
    throw unimpl();
  }

  // Swap a New and a Call, when we cannot use a Split/Join.
  private Node swap_new(Node cepim, MrgProjNode mrg ) {
    cepim.keep();
    cepim.insert(mrg);
    set_def(1,mrg.mem());
    mrg.set_def(1,cepim.unkeep());
    Env.GVN.revalive(mrg);
    Env.GVN.add_flow_uses(mrg);
    Env.GVN.add_flow(this);
    Env.GVN.add_flow(cepim.in(0));
    return this;
  }

  // Pass thru all inputs directly - just a direct gather/scatter.  The gather
  // enforces SESE which in turn allows more precise memory and aliasing.  The
  // full scatter lets users decide the meaning; e.g. wired FunNodes will take
  // the full arg set but if the call is not reachable the FunNode will not
  // merge from that path.  Result tuple type:
  @Override public Type value() {
    // Pinch to XCTRL/CTRL
    Type ctl = ctl()._val;
    if( ctl != Type.CTRL ) return ctl.oob();
    // Not a function to call?
    Type tfx = fdx()._val;
    if( !(tfx instanceof TypeFunPtr) ) return tfx.oob();

    // Not a memory to the call?
    Type mem = mem()==null ? TypeMem.ANYMEM : mem()._val;
    TypeMem tmem = mem instanceof TypeMem ? (TypeMem)mem : mem.oob(TypeMem.ALLMEM);

    // Result type includes a type-per-input and an extra roll-up type of all
    // escaping aliases.
    final Type[] ts = Types.get(_defs._len+1/*+1 tescs turned off*/);
    ts[CTL_IDX] = Type.CTRL;
    ts[MEM_IDX] = tmem;         // Memory into the callee, not caller

    // Copy args for called functions.  FIDX is already refined.
    // Also gather all aliases from all args.
    TypeFunPtr tfp = (TypeFunPtr)tfx;
    ts[DSP_IDX] = tfp._dsp;
    //BitsAlias as = get_alias(tfp._dsp);
    for( int i=ARG_IDX; i<nargs(); i++ )
      ts[i] = arg(i)==null ? Type.XSCALAR : arg(i)._val;    
    if( !(fdx() instanceof FunPtrNode) )
      tfp = (TypeFunPtr)((UnresolvedNode)fdx()).resolve_value(ts)._val;
    ts[_defs._len] = tfp;
    return TypeTuple.make(ts);
  }
  // Get (shallow) aliases from the type
  private BitsAlias get_alias( Type t ) {
    if( t instanceof TypeMemPtr ) return ((TypeMemPtr)t)._aliases;
    if( TypeMemPtr.OOP.isa(t)   ) return BitsAlias.FULL;
    return BitsAlias.EMPTY;
  }

  @Override BitsAlias escapees() {
    //BitsAlias esc_in  = tesc(_val)._aliases;
    //CallEpiNode cepi = cepi();
    //TypeTuple tcepi = cepi._val instanceof TypeTuple ? (TypeTuple) cepi._val : (TypeTuple) cepi._val.oob(TypeTuple.CALLE);
    //BitsAlias esc_out = CallEpiNode.esc_out((TypeMem)tcepi.at(1),tcepi.at(2));
    //TypeMem precall = (TypeMem) mem()._val;
    //BitsAlias esc_out2 = precall.and_unused(esc_out); // Filter by unused pre-call
    //return esc_out2.meet(esc_in);
    throw unimpl();
  }
  @Override public void add_flow_extra(Type old) {
    if( old==Type.ANY || _val==Type.ANY ||
        (old instanceof TypeTuple && ttfp(old).above_center()) )
      add_flow_defs();      // Args can be more-alive or more-dead
    // If Call flips to being in-error, all incoming args forced live/escape
    for( Node def : _defs )
      if( def!=null && err(true)!=null )
        Env.GVN.add_flow(def);
    // If not resolved, might now resolve
    if( _val instanceof TypeTuple && ttfp(_val)._fidxs.abit()==-1 )
      Env.GVN.add_reduce(this);
    // If escapes lowers, can allow e.g. swapping with New
    //if( _val instanceof TypeTuple && tesc(old)!=tesc(_val) )
    //  Env.GVN.add_grow(this);
  }

  @Override public void add_flow_def_extra(Node chg) {
    // Projections live after a call alter liveness of incoming args
    if( chg instanceof ProjNode )
      Env.GVN.add_flow(in(((ProjNode)chg)._idx));
  }

  @Override public void add_flow_use_extra(Node chg) {
    CallEpiNode cepi = cepi();
    if( chg == fdx() ) {           // FIDX falls to sane from too-high
      add_flow_defs();             // All args become alive
      if( cepi!=null ) {
        Env.GVN.add_work_new (cepi); // FDX gets stable, might wire, might unify_lift
        Env.GVN.add_flow_defs(cepi); // Wired Rets might no longer be alive (might unwire)
      }
    } else if( chg == mem() ) {
      if( cepi != null ) Env.GVN.add_flow(cepi);
    } else {                    // Args lifted, may resolve
      if( fdx() instanceof UnresolvedNode )
        Env.GVN.add_reduce(this);
    }
  }

  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live_use(Node def) {
    TypeMem basic_live = def._live.basic_live() ? TypeMem.ALIVE : TypeMem.ALLMEM;
    if( is_keep() ) return basic_live; // Still under construction, all alive
    Type tcall = _val;
    if( !(tcall instanceof TypeTuple) ) // Call is has no value (yet)?
      return tcall.oob(basic_live);

    if( def==ctl() ) return TypeMem.ALIVE;
    if( def==mem() ) return _live;

    CallEpiNode cepi = cepi();
    if( def==fdx() ) {          // Function argument
      if( _is_copy ) return TypeMem.DEAD;
      TypeFunPtr tfp = ttfp(tcall);
      BitsFun fidxs = tfp.fidxs();
      // If using a specific FunPtr and its in the resolved set, test more precisely
      RetNode ret;
      if( def instanceof FunPtrNode &&           // Have a FunPtr
          (ret=((FunPtrNode)def).ret())!=null && // Well-structured function
          !fidxs.test_recur(ret._fidx) )         // FIDX directly not used
        //return TypeMem.DEAD;                     // Not in the fidx set.
        throw unimpl();    // premature optimization?
      // Otherwise, the FIDX is alive.  Check the display.
      ProjNode dsp = ProjNode.proj(this,DSP_IDX);
      return (cepi==null || !cepi.is_all_wired() || // Unwired calls remain, dsp could be alive yet
              (dsp!=null && dsp._live==TypeMem.ALIVE)) ? TypeMem.ALIVE : TypeMem.LNO_DISP;
    }

    // Check that all fidxs are wired; an unwired fidx might be in-error
    // and we want the argument alive for errors.  This is a value turn-
    // around point (high fidxs need to fall)
    if( !_is_copy && !cepi.is_all_wired() ) return TypeMem.ALIVE;
    // All wired, the arg is dead if the matching projection is dead
    int argn = _defs.find(def);
    ProjNode proj = ProjNode.proj(this, argn);
    return proj == null || proj._live == TypeMem.DEAD ? TypeMem.DEAD : TypeMem.ALIVE;
  }

  @Override public TV2 new_tvar( String alloc_site) { return null; }

  // See if we can resolve an unresolved Call
  @Override public void combo_resolve(WorkNode ambi) {
    if( _live == TypeMem.DEAD ) return;
    // Wait until the Call is reachable
    if( ctl()._val != Type.CTRL || !(_val instanceof TypeTuple) ) return;
    // Only ambiguous if FIDXs are both above_center and there are more than one
    BitsFun fidxs = ttfp(_val).fidxs();
    if( !fidxs.above_center() || fidxs.abit() != -1 ) return;
    // Track ambiguous calls: resolve after GCP gets stable, and if we
    // can resolve we continue to let GCP fall.
    ambi.add(this);
  }

  @Override public ErrMsg err( boolean fast ) {
    // Fail for passed-in unknown references directly.
    for( int j=ARG_IDX; j<nargs(); j++ )
      if( arg(j) instanceof UnresolvedNode && arg(j)._defs._len==0 )
        return fast ? ErrMsg.FAST : ErrMsg.forward_ref(_badargs[j-ARG_IDX+1], FunNode.find_fidx(((FunPtrNode)arg(j)).ret()._fidx).fptr());

    // Expect a function pointer
    TypeFunPtr tfp = ttfp(_val);
    if( tfp._fidxs==BitsFun.FULL ) {
      if( fast ) return ErrMsg.FAST;
      return ErrMsg.unresolved(_badargs[0],"A function is being called, but "+fdx()._val+" is not a function type");
    }

    BitsFun fidxs = tfp.fidxs();
    if( fidxs.above_center() ) return null; // Not resolved (yet)
    if( fidxs.is_empty() ) // This is an unresolved call
      throw unimpl();

    // bad-arg-count
    if( tfp.nargs() != nargs() )
      return fast ? ErrMsg.FAST : ErrMsg.syntax(_badargs[0],"Passing "+(nargs()-ARG_IDX)+" arguments to "+tfp.names(false)+" which takes "+(tfp.nargs()-ARG_IDX)+" arguments");

    return null;
  }

  public CallEpiNode cepi() {
    for( Node cepi : _uses )    // Find CallEpi for bypass aliases
      if( cepi instanceof CallEpiNode )
        return (CallEpiNode)cepi;
    return null;
  }

  @Override public Node is_copy(int idx) {
    if( !_is_copy ) return null;
    if( _val==Type.ANY ) return Env.ANY;
    if( idx!=DSP_IDX ) return in(idx);
    // The display out of a Call is the FunPtr in to the Call.
    // Map to the FunPtr to the Display.
    if( fdx() instanceof FunPtrNode )  return ((FunPtrNode)fdx()).display();
    else throw unimpl(); // Need a FP2DISP
  }
  void set_rpc(int rpc) { unelock(); _rpc=rpc; } // Unlock before changing hash
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }
  public Node[] parms() {
    return _defs._len>= DSP_IDX ? Arrays.copyOf(_defs._es,_defs._len-1) : new Node[0]; // All defs, except the FIDX.
  }
}
