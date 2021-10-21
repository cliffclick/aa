package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;

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
    if( !(tcall instanceof TypeTuple) ) return tcall.oob(TypeMemPtr.OOP);
    TypeTuple tt = (TypeTuple)tcall;
    return (TypeMemPtr)tt.at(tt.len()-1);
  }
  // No-check must-be-correct get TFP
  static public TypeFunPtr ttfp( Type t ) {
    if( !(t instanceof TypeTuple) ) return (TypeFunPtr)t.oob(TypeFunPtr.GENERIC_FUNPTR);
    TypeTuple tcall = (TypeTuple)t;
    return (TypeFunPtr)tcall.at(tcall.len()-2);
  }
  static TypeTuple set_ttfp( TypeTuple tcall, TypeFunPtr nfptr ) { return tcall.set(tcall.len()-2,nfptr); }
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
            add_def( nnn.in(i));
          _unpacked = true;      // Only do it once
          keep().xval();         // Recompute value, this is not monotonic since replacing tuple with args
          GVN.add_work_all(unkeep());// Revisit after unpacking
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


    // If the function is unresolved, see if we can resolve it now.
    // Fidxs are typically low during iter, but can be high during
    // iter post-GCP on error calls where nothing resolves.
    Node fdx = fdx();           // Function epilog/function pointer
    int fidx = fidxs.abit();    // Check for single target
    //if( fidx == -1 && !fidxs.above_center() && !fidxs.test(1)) {
    //  FunPtrNode fptr = least_cost(fidxs, fdx); // Check for least-cost target
    //  if( fptr != null ) {
    //    if( cepi!=null ) Env.GVN.add_reduce(cepi); // Might unwire
    //    set_fdx(fptr);          // Resolve to 1 choice
    //    xval();                 // Force value update; least-cost LOWERS types (by removing a choice)
    //    add_work_use_extra(Env.GVN._work_flow,fptr);
    //    if( cepi!=null ) Env.GVN.add_reduce(cepi); // Might unwire
    //    return this;
    //  }
    //}

    // If we have a single function allowed, force the function constant.
    if( fidx != -1 && !(fdx instanceof FunPtrNode) ) {
      // Check that the single target is well-formed
      FunNode fun = FunNode.find_fidx(Math.abs(fidx));
      if( fun != null && !fun.is_dead() ) {
        RetNode ret = fun.ret();
        if( ret != null ) {
          // The same function might be called with different displays; make
          // sure we get the right one.  See if there is a single un-escaped
          // FunPtr.  Common for non-upwardsly exposed targets.
          FunPtrNode fptr = ret.funptr();
          if( fptr != null && !fptr.display()._live.live().is_escape() )
            throw unimpl(); //return set_dsp(fptr);
          // See if FunPtr is available just above an Unresolved.
          if( fdx instanceof UnresolvedNode ) {
            fptr = ((UnresolvedNode)fdx).find_fidx(fidx);
            if( fptr != null ) { // Gonna improve
              return set_fdx(fptr);
            }
          }
        }
      }
    }

    // Wire valid targets.
    CallEpiNode cepi = cepi();
    if( cepi!=null && cepi.check_and_wire(Env.GVN._work_flow) )
      return this;              // Some wiring happened

    // Check for dead args and trim; must be after all wiring is done because
    // unknown call targets can appear during GCP and use the args.  After GCP,
    // still must verify all called functions have the arg as dead, because
    // alive args still need to resolve.  Constants are an issue, because they
    // fold into the Parm and the Call can lose the matching DProj while the
    // arg is still alive.
    if( GVN._opt_mode._CG && err(true)==null ) {
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
    if( _keep>0 || cepi==null || !(mem._val instanceof TypeMem) ) return null;
    ProjNode cepim = ProjNode.proj(cepi,MEM_IDX); // Memory projection from CEPI
    ProjNode cepid = ProjNode.proj(cepi,REZ_IDX); // Return projection from CEPI
    if( cepim == null ) return null;
    if( !(cepim._val instanceof TypeMem) ) return null;
    TypeMem tmcepi = (TypeMem) cepim._val;
    if( !mem._val.isa(tmcepi) ) return null; // Call entry stale relative to exit
    BitsAlias escs = escapees();
    // Check for prior      MrgProj/New
    if( mem instanceof MrgProjNode )
      return _ideal_grow((MrgProjNode)mem,cepim,cepid,escs,-1);
    // Check for prior Join/MrgProj/New
    if( mem instanceof MemJoinNode ) {
      if( !mem.check_solo_mem_writer(this) )
        return null;
      for( int i=1; i<mem._defs._len; i++ )
        if( mem.in(i) instanceof MrgProjNode ) {
          Node x = _ideal_grow((MrgProjNode)mem.in(i),cepim,cepid,escs,i);
          if( x!=null ) return x;
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
    if( mem._uses._len==2 && mem._uses.find(Env.DEFMEM)==-1 ) return null; // Something other than DEFMEM

    // If call returns same as new (via recursion), cannot split, but CAN swap.
    TypeMem tmcepi = (TypeMem) cepim._val;
    BitsAlias esc_out = CallEpiNode.esc_out(tmcepi,cepid==null ? Type.XNIL : cepid._val);
    BitsAlias escs2 = escs.meet(esc_out);
    Node jn = mem();
    if( !escs2.is_empty() && !esc_out.test_recur(alias) ) { // No return conflict, so parallelize memory
      if( jn==mem )             // Bare Call/New; add a Split/Join.
        return MemSplitNode.insert_split(cepim,escs2,this,mem,mem);
      return null; // TODO: allow Call to move into existing JOIN
    } else {                    // Else move New below Call.
      if( jn!=mem ) {           // Move New below Join
        Node pre = mem.mem();
        jn.set_def(i,pre);
        mem.set_def(MEM_IDX,jn);
        set_mem(mem);
        Env.GVN.add_unuse(jn);
        Env.GVN.add_unuse(mem);
      }
      return swap_new(cepim,mem); // Move New below Call
    }
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
  @Override public Type value(GVNGCM.Mode opt_mode) {
    // Pinch to XCTRL/CTRL
    Type ctl = ctl()._val;
    if( ctl != Type.CTRL ) return ctl.oob();

    // Not a memory to the call?
    Type mem = mem()==null ? TypeMem.ANYMEM : mem()._val;
    TypeMem tmem = mem instanceof TypeMem ? (TypeMem)mem : mem.oob(TypeMem.ALLMEM);

    // Result type includes a type-per-input and an extra roll-up type of all
    // escaping aliases.
    final Type[] ts = Types.get(_defs._len+2);
    ts[CTL_IDX] = Type.CTRL;
    ts[MEM_IDX] = tmem;         // Memory into the callee, not caller

    // Not a function to call?
    Type tfx = fdx()==null ? TypeFunPtr.GENERIC_FUNPTR : fdx()._val;
    if( !(tfx instanceof TypeFunPtr) )
      tfx = tfx.oob(TypeFunPtr.GENERIC_FUNPTR);
    TypeFunPtr tfp = (TypeFunPtr)tfx;
    BitsFun fidxs = tfp.fidxs();
    BitsFun fidxs2 = least_cost2(fidxs);
    if( fidxs != fidxs2 ) {
      Type tret = tfp._ret;
      // Cannot match Unresolved, because fidxs flow infinitely far, and
      // if the FunPtr sharpens return type, this is not a neighbor.
      //for( int fidx : fidxs2 ) { // Code matches UnresolvedNode
      //  Type rez = ((TypeFunPtr)FunNode.find_fidx(fidx).fptr()._val)._ret;
      //  tret = fidxs2.above_center() ? tret.join(rez) : tret.meet(rez);
      //}
      tfp = TypeFunPtr.make(fidxs2,tfp._nargs,tfp._dsp,tret);
    }
    //if( fidxs.above_center() && tfp!=TypeFunPtr.GENERIC_FUNPTR.dual() ) {
    //  if( _not_resolved_by_gcp ) { // If overloads not resolvable, then take them all, and we are in-error
    //    tfp = tfp.make_from(fidxs.dual()); // Force FIDXS low (take all), and we are in-error
    //  } else {
    //    FunPtrNode fptr = least_cost(fidxs,fdx());
    //    if( fptr!=null )
    //      tfp = (TypeFunPtr)fptr._val;
    //  }
    //}

    // Copy args for called functions.  FIDX is already refined.
    // Also gather all aliases from all args.
    ts[DSP_IDX] = tfp._dsp;
    BitsAlias as = get_alias(tfp._dsp);
    for( int i=ARG_IDX; i<nargs(); i++ )
      as = as.meet(get_alias(ts[i] = arg(i)==null ? Type.XSCALAR : arg(i)._val));
    // Recursively search memory for aliases; compute escaping aliases
    BitsAlias as2 = tmem.all_reaching_aliases(as);
    ts[_defs._len  ] = tfp;
    ts[_defs._len+1] = TypeMemPtr.make(as2,TypeObj.ISUSED); // Set escapes as last type
    // Only pass along escaping aliases; others are not available to the call
    // body.  In the case of recursive calls, aliases made new in the body may
    // not be passed into the recursive calls, and thus not into the call head
    // and thus avoids self-merging.  Once we decide to inline, keep the entire
    // alias set since this filtering by the CallNode goes away as we inline.
    if( !_is_copy ) ts[MEM_IDX] = tmem.slice_reaching_aliases(as2);

    return TypeTuple.make(ts);
  }
  // Get (shallow) aliases from the type
  private BitsAlias get_alias( Type t ) {
    if( t instanceof TypeMemPtr ) return ((TypeMemPtr)t)._aliases;
    if( TypeMemPtr.OOP.isa(t)   ) return BitsAlias.FULL;
    return BitsAlias.EMPTY;
  }

  @Override BitsAlias escapees() {
    BitsAlias esc_in  = tesc(_val)._aliases;
    CallEpiNode cepi = cepi();
    TypeTuple tcepi = cepi._val instanceof TypeTuple ? (TypeTuple) cepi._val : (TypeTuple) cepi._val.oob(TypeTuple.CALLE);
    BitsAlias esc_out = CallEpiNode.esc_out((TypeMem)tcepi.at(1),tcepi.at(2));
    TypeMem precall = (TypeMem) mem()._val;
    BitsAlias esc_out2 = precall.and_unused(esc_out); // Filter by unused pre-call
    return esc_out2.meet(esc_in);
  }
  @Override public void add_work_extra(Work work, Type old) {
    if( old==Type.ANY || _val==Type.ANY ||
        (old instanceof TypeTuple && ttfp(old).above_center()) )
      add_work_defs(work);      // Args can be more-alive or more-dead
    // If Call flips to being in-error, all incoming args forced live/escape
    for( Node def : _defs )
      if( def!=null && def._live!=TypeMem.ESCAPE && err(true)!=null )
        work.add(def);
    // If not resolved, might now resolve
    if( _val instanceof TypeTuple && ttfp(_val)._fidxs.abit()==-1 )
      Env.GVN.add_reduce(this);
    // If escapes lowers, can allow e.g. swapping with New
    if( _val instanceof TypeTuple && tesc(old)!=tesc(_val) )
      Env.GVN.add_grow(this);
  }

  @Override public void add_work_def_extra(Work work, Node chg) {
    // Projections live after a call alter liveness of incoming args
    if( chg instanceof ProjNode )
      work.add(in(((ProjNode)chg)._idx));
  }

  @Override public void add_work_use_extra(Work work, Node chg) {
    CallEpiNode cepi = cepi();
    if( chg == fdx() ) {           // FIDX falls to sane from too-high
      add_work_defs(work);         // All args become alive
      if( cepi!=null ) {
        Env.GVN.add_work_all(cepi);  // FDX gets stable, might wire, might unify_lift
        work.add(cepi);
        cepi.add_work_defs(work); // Wired Rets might no longer be alive (might unwire)
      }
    } else if( chg == mem() ) {
      if( cepi != null ) work.add(cepi);
    } else {                    // Args lifted, may resolve
      if( fdx() instanceof UnresolvedNode )
        Env.GVN.add_reduce(this);
      ErrMsg err = err(true);
      if( err==null ) work.add(cepi); // Call goes from err -> not_err, CEPI makes progress
      if( Env.GVN._opt_mode._CG && err==null )
        work.add(mem());        // Call not-in-error, memory may lift
      if( Env.GVN._opt_mode._CG && err!=null )
        add_work_defs(work);    // Call in-error, all args are now used
    }
  }

  // Compute live across uses.  If pre-GCP, then we may not be wired and thus
  // have not seen all possible function-body uses.  Check for #FIDXs == nwired().
  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    if( !opt_mode._CG ) {
      BitsFun fidxs = ttfp(_val).fidxs();
      if( fidxs.above_center() ) return _live; // Got choices, dunno which one will stick
      CallEpiNode cepi = cepi();
      if( cepi==null ) return _live; // Collapsing
      if( ctl()._val == Type.XCTRL ) return _live; // Unreachable
      // Expand (actually fail) if any parents
      BitSet bs = fidxs.tree().plus_kids(fidxs);
      if( bs.cardinality() > cepi.nwired() ) // More things to call
        return _live; // Cannot improve
    }
    // All choices discovered during GCP.  If the call is in-error it may not
    // resolve and so will have no uses other than the CallEpi - which is good
    // enough to declare this live, so it exists for errors.
    return super.live(opt_mode);
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {

    if( def==fdx() ) {                         // Function argument
      if( def instanceof ThretNode ) return TypeMem.ALLMEM; // Always inlines eagerly, so this is always temporary
      if( !opt_mode._CG ) return TypeMem.ESCAPE; // Prior to GCP, assume all fptrs are alive and display escapes
      Type tcall = _val;
      if( !(tcall instanceof TypeTuple) ) // Call is has no value (yet)?
        return tcall.above_center() ? TypeMem.DEAD : TypeMem.ESCAPE;
      TypeFunPtr tfp = ttfp(tcall);
      BitsFun fidxs = tfp.fidxs();
      // If using a specific FunPtr and its in the resolved set, test more precisely
      RetNode ret;
      if( def instanceof FunPtrNode &&           // Have a FunPtr
          (ret=((FunPtrNode)def).ret())!=null && // Well-structured function
          !fidxs.test_recur(ret._fidx) )         // FIDX directly not used
        return TypeMem.DEAD;                     // Not in the fidx set.
      // Otherwise, the FIDX is alive.  Check the display.
      ProjNode dsp = ProjNode.proj(this,DSP_IDX);
      return dsp!=null && dsp._live==TypeMem.ALIVE ? TypeMem.ALIVE : TypeMem.LNO_DISP;
    }

    if( def==ctl() ) return TypeMem.ALIVE;

    if( def!=mem() ) {         // Some argument
      // Check that all fidxs are wired; an unwired fidx might be in-error
      // and we want the argument alive for errors.  This is a value turn-
      // around point (high fidxs need to fall)

      // Pre GCP, might not wire (yet), assume fully used by unwired valid fcn
      // target, so ESCAPE.

      // 1st GCP, wiring appears over time, if not wired assume it will be and
      // do the optimistic proj test.

      // Post GCP, if not wired, then Call is in error, so ESCAPE.
      if( opt_mode._CG && _val==Type.ANY ) return TypeMem.DEAD;
      if( opt_mode._CG &&       // Either mid-GCP or post-GCP
           (err(true)==null &&  // Not in-error
            // And fully wired (no new users will wire)
            (opt_mode==GVNGCM.Mode.Opto || all_fcns_wired()) ) ) {
        int argn = _defs.find(def);
        ProjNode proj = ProjNode.proj(this, argn);
        if( proj == null || proj._live == TypeMem.DEAD )
          return TypeMem.DEAD; // Arg not used
      }
      if( def instanceof ThretNode ) return TypeMem.ALLMEM;
      assert def.all_live().basic_live();
      return TypeMem.ESCAPE;    // Args always alive and escape
    }

    // After we have the exact callers, use liveness directly.  True if we have
    // the Call Graph, or the callers are known directly.  If the call is
    // in-error, act as-if we do not know the Call Graph.
    if( !(_val instanceof TypeTuple) ) // No type to sharpen
      return _val.oob(TypeMem.ALLMEM);
    if( opt_mode._CG || fdx() instanceof FunPtrNode ) // All callers known
      return err(true)==null ? _live : TypeMem.ALLMEM; // Use live directly (unless in error)

    // Unknown future callees act as-if all available aliases are read from and
    // thus live.
    BitsAlias aliases = BitsAlias.EMPTY;
    for( int i=DSP_IDX; i<nargs(); i++ ) {
      Type targ = targ(_val,i);
      if( TypeMemPtr.OOP.isa(targ) )
        { aliases=BitsAlias.FULL; break; } // All possible pointers, so all memory is alive
      if( !(targ instanceof TypeMemPtr) ) continue; // Not a pointer, does not need memory to sharpen
      if( targ.above_center() ) continue; // Have infinite choices still, no memory
      aliases = aliases.meet(((TypeMemPtr)targ)._aliases);
    }
    // Conservative too strong; need only memories that go as deep as the
    // formal types.
    TypeMem caller_mem = emem(_val);
    TypeMem tmem2 = caller_mem.slice_reaching_aliases(caller_mem.all_reaching_aliases(aliases));
    return (TypeMem)tmem2.meet(_live);
  }

  private boolean all_fcns_wired() {
    BitsFun fidxs = ttfp(_val)._fidxs;
    if( _is_copy || fidxs==BitsFun.FULL ) return true;
    CallEpiNode cepi = cepi();
    return cepi != null && fidxs.bitCount() <= cepi.nwired();
  }

  // Resolve choice calls based on the left arg.
  public BitsFun least_cost2(BitsFun choices) {
    if( choices==BitsFun.EMPTY || choices==BitsFun.FULL|| choices==BitsFun.ANY  || choices.abit() != -1 )
      return choices;  // Too many, zero or one choice - nothing to improve
    Type actual = val(ARG_IDX);
    BitsFun fdxs = BitsFun.EMPTY;
    final boolean hi = choices.above_center();
    // For low ties amongst int and float, always lift to int
    int fi=0, ff=0, fx=0;
    for( int fidx : choices ) {
      // Parent/kids happen during inlining
      for( int kidx=fidx; kidx!=0; kidx=BitsFun.next_kid(fidx,kidx) ) {
        FunNode fun = FunNode.find_fidx(kidx);
        if( fun==null || fun.is_dead() || fun.nargs()!=nargs() || fun.in(0)==fun ) continue; // BAD/dead
        Type formal = fun.formals().fld_idx(ARG_IDX)._t;
        boolean isa = actual.isa(formal);
        if( isa || (!hi && formal.isa(actual)) ) {
          BitsFun fdxs0 = pairwise_above(fdxs,kidx,formal);
          if( fdxs0 != fdxs ) { // Progress?
            fdxs = fdxs0;       // Keep progress
            if( isa ) {
              if( formal instanceof TypeInt ) fi = kidx;
              else if( formal instanceof TypeFlt ) ff = kidx;
              else fx = kidx;   // Something else
            } else {
              fx = kidx;        // Something failed the isa test
            }
          }
        }
      }
    }

    if( (!hi || !Combo.HM_IS_HIGH ) && fi!=0 && ff!=0 && fx==0 ) {
      fdxs = fdxs.clear(ff);
    }
    if( hi && fdxs.abit()== -1 )
      fdxs = fdxs.dual();
    return fdxs;
  }

  // Pairwise, toss out any fidx who's first formal is dominated by this formal
  // or vice-versa, or toss this fidx in otherwise.
  private static BitsFun pairwise_above(BitsFun fidxs, int nidx, Type nformal) {
    for( int fidx : fidxs ) {
      Type formal = FunNode.find_fidx(fidx).formals().fld_idx(ARG_IDX)._t;
      if( nformal.isa(formal) )
        return fidxs.clear(fidx).set(nidx); // Keep the tighter bounds
      if( formal.isa(nformal) )
        return fidxs;           // Keep the tigher bounds
    }
    return fidxs.set(nidx);     // Extend
  }


  // Amongst these choices return the least-cost.  Some or all might be invalid.
  public FunPtrNode least_cost(BitsFun choices, Node unk) {
    if( choices==BitsFun.EMPTY ) return null;
    assert choices.bitCount() > 0; // Must be some choices
    assert choices.abit()!= -1 || (choices.above_center() == (GVN._opt_mode==GVNGCM.Mode.Opto));
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
        if( fun==null || fun.is_dead() || fun.nargs()!=nargs() || fun.in(0)==fun ) continue; // BAD/dead
        TypeStruct formals = fun.formals(); // Type of each argument
        int cvts=0;                         // Arg conversion cost
        for( TypeFld fld : formals.flds() ) {
          Type formal = fld._t;
          Type actual = arg(fld._order)._val;
          if( fld.is_display_ptr() && actual instanceof TypeFunPtr )
            actual = ((TypeFunPtr)actual)._dsp;
          if( actual==formal ) continue;
          if( fld._order <= MEM_IDX ) continue; // isBitShape not defined on memory
          if( Type.ALL==formal ) continue; // Allows even error arguments
          byte cvt = actual.isBitShape(formal); // +1 needs convert, 0 no-cost convert, -1 unknown, 99 never
          if( cvt == -1 ) return null; // Might be the best choice, or only choice, dunno
          cvts += cvt;
        }

        if( cvts < 99 && cvts < best_cvts ) {
          best_cvts = cvts;
          best_fptr = get_fptr(fun,unk); // This can be null, if function is run-time computed & has multiple displays.
          best_formals = formals;
          tied=false;
        } else if( cvts==best_cvts ) {
          // Look for monotonic formals
          int fcnt=0, bcnt=0;
          for( TypeFld fld : formals.flds() ) {
            TypeFld best_fld = best_formals.fld_find(fld._fld);
            if( best_fld==null ) { fcnt=bcnt=-1; break; } // Not monotonic, no obvious winner
            Type ff = fld._t, bf = best_fld._t;
            if( ff==bf ) continue;
            Type mt = ff.meet(bf);
            if( ff==mt ) bcnt++;       // Best formal is higher than new
            else if( bf==mt ) fcnt++;  // New  formal is higher than best
            else { fcnt=bcnt=-1; break; } // Not monotonic, no obvious winner
          }
          // If one is monotonically higher than the other, take it
          if( fcnt > 0 && bcnt==0 ) { best_fptr = get_fptr(fun,unk); best_formals = formals; }
          else if( fcnt != 0 || bcnt <= 0 ) tied = true; // Tied, ambiguous
          // Keep current
        }
      }
    }
    if( best_cvts >= 99 ) return null; // No valid functions
    return tied ? null : best_fptr; // Ties need to have the ambiguity broken another way
  }
  static FunPtrNode get_fptr(FunNode fun, Node unk) {
    RetNode ret = fun.ret();
    FunPtrNode fptr = ret.funptr();
    if( fptr != null ) return fptr; // Only one choice
    if( !(unk instanceof UnresolvedNode) ) return null; // No selection of fptrs to pick from
    for( Node def : unk._defs )
      if( ((FunPtrNode)def).ret()== ret )
        return (FunPtrNode)def;
    return null;
  }

  @Override public TV2 new_tvar( String alloc_site) { return null; }

  // Resolve a call, removing ambiguity during the GCP/Combo pass.
  @Override public boolean remove_ambi(Ary<Node> oldfdx) {
    BitsFun fidxs = ttfp(_val).fidxs();
    if( !fidxs.above_center() ) return true ; // Resolved after all
    if( fidxs == BitsFun.ANY )  return false; // Too many choices, no progress
    return false;
    // TODO Yank this whole method
    //// Pick least-cost among choices
    //Node fdx = fdx();
    //FunPtrNode fptr = least_cost(fidxs,fdx);
    //if( fptr==null ) return false; // Not resolved, no progress
    //oldfdx.push(fdx.keep());       // Keep current liveness until the end of Combo
    //set_fdx(fptr);                 // Set resolved edge
    //return true;                   // Progress
  }

  // See if we can resolve an unresolved Call
  @Override public void combo_resolve(Work ambi) {
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
      if( arg(j)!=null && arg(j).is_forward_ref() )
        return fast ? ErrMsg.FAST : ErrMsg.forward_ref(_badargs[j-ARG_IDX+1], FunNode.find_fidx(((FunPtrNode)arg(j)).ret()._fidx).fptr());
    // Expect a function pointer
    TypeFunPtr tfp = ttfp(_val);
    if( tfp._fidxs==BitsFun.FULL ) {
      if( fast ) return ErrMsg.FAST;
      return ErrMsg.unresolved(_badargs[0],"A function is being called, but "+fdx()._val+" is not a function type");
    }

    // Indirectly, forward-ref for function type
    if( tfp.is_forward_ref() ) // Forward ref on incoming function
      return fast ? ErrMsg.FAST : ErrMsg.forward_ref(_badargs[0], FunNode.find_fidx(tfp.fidx()).fptr());

    BitsFun fidxs = tfp.fidxs();
    if( fidxs.above_center() ) return null; // Not resolved (yet)
    Type tfdx;
    if( fidxs.is_empty() ) {// This is an unresolved call
      if( fast ) return ErrMsg.FAST;
      // See if we can find some FIDX choices to give a better error message
      if( (tfdx=fdx()._val) instanceof TypeFunPtr ) {
        BitsFun fx = ((TypeFunPtr)tfdx)._fidxs;
        if( fx.above_center() ) { fidxs = fx; tfp = tfp.make_from(fx); }
      }
    }

    // bad-arg-count
    if( tfp._nargs != nargs() )
      return fast ? ErrMsg.FAST : ErrMsg.syntax(_badargs[0],"Passing "+(nargs()-ARG_IDX)+" arguments to "+tfp.names(false)+" which takes "+(tfp._nargs-ARG_IDX)+" arguments");

    // Call did not resolve.
    if( fidxs.is_empty() )
      return ErrMsg.unresolved(_badargs[0],"Unable to resolve call");

    // Also happens if more than one FIDX shares the same Unresolved.
    // Basically means we did not clone enough to remove a choice amongst primitives.
    // Bail out here if we see more than one Unresolved.
    Node munr = null;
    for( int fidx : fidxs ) {                    // All fidxs to Call
      FunNode fun = FunNode.find_fidx(fidx);
      if( fun==null || fun.is_dead() || fun.ret()==null ) continue; // No such function (probably dead and mid-cleanup)
      outer:
      for( Node fptrs : fun.ret()._uses )      // FunPtrs for each fidx (typically 1)
        if( fptrs instanceof FunPtrNode )
          for( Node unr : fptrs._uses )          // Unresolved behind each FunPtr (typically 1)
            if( unr instanceof UnresolvedNode && // Unresolved includes fdxs in this Call FDX set?
                unr._val instanceof TypeFunPtr &&
                ((TypeFunPtr)(tfp.join(unr._val)))._fidxs.abit() == -1 ) {
              if( munr == null || munr._val==unr._val ) { munr = unr; continue outer; }
              return fast ? ErrMsg.FAST : ErrMsg.unresolved(_badargs[0],"Unable to resolve call");
            }
    }

    // Now do an arg-check.  No more than 1 unresolved, so the error message is
    // more sensible.
    BitsFun.Tree<BitsFun> tree = fidxs.tree();
    for( int j=ARG_IDX; j<nargs(); j++ ) {
      Type actual = arg(j).sharptr(mem());
      Ary<Type> ts=null;
      for( int fidx : fidxs ) {
        if( fidx==0 ) continue;
        for( int kid=fidx; kid!=0; kid = tree.next_kid(fidx,kid) ) {
          FunNode fun = FunNode.find_fidx(kid);
          if( fun==null || fun.is_dead() ) continue;
          TypeStruct formals = fun.formals(); // Type of each argument
          if( fun.parm(j)==null ) continue;   // Formal is dead
          Type formal = formals.fld_idx(j)._t;
          if( actual.isa(formal) ) continue; // Actual is a formal
          if( fast ) return ErrMsg.FAST;     // Fail-fast
          if( ts==null ) ts = new Ary<>(new Type[1],0);
          if( ts.find(formal) == -1 ) // Dup filter
            ts.push(formal);          // Add broken type
        }
      }
      if( ts!=null )
        return ErrMsg.typerr(_badargs[j-ARG_IDX+1],actual, mem()._val,ts.asAry());
    }

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
  @Override Node is_pure_call() { return fdx().is_pure_call()==null ? null : mem(); }
  public Node[] parms() {
    return _defs._len>= DSP_IDX ? Arrays.copyOf(_defs._es,_defs._len-1) : new Node[0]; // All defs, except the FIDX.
  }
}
