package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
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
  // Example: call(arg1,arg2)
  // _badargs[0] points to the opening paren.
  // _badargs[1] points to the start of arg1, same for arg2, etc.
  Parse[] _badargs;         // Errors for e.g. wrong arg counts or incompatible args; one error point per arg.

  public CallNode( boolean unpacked, Parse[] badargs, Node... defs ) {
    super(OP_CALL,defs);
    _rpc = BitsRPC.new_rpc(BitsRPC.ALLX); // Unique call-site index
    _unpacked=unpacked;         // Arguments are typically packed into a tuple and need unpacking, but not always
    _badargs = badargs;
  }

  @Override public String xstr() { return (_is_copy ? "CopyCall" : (is_dead() ? "Xall" : "Call")); } // Self short name
  String  str() { return xstr(); }       // Inline short name
  @Override boolean is_CFG() { return !_is_copy; }
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
  public CallNode set_fdx( Node fun) { set_def(DSP_IDX, fun); return this; }
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
    if( !(t instanceof TypeTuple tcall) ) return (TypeFunPtr)t.oob(TypeFunPtr.GENERIC_FUNPTR);
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
    if( !_unpacked &&           // Not yet unpacked a tuple
        val(ARG_IDX) instanceof TypeStruct ts && // An arg collection
        ts.is_tup() ) {                          // A tuple
      // Find a tuple being passed in directly; unpack
      Node nnn = pop(); // Pop off the tuple
      if( nnn instanceof StructNode )
        for( Node n : nnn._defs ) // Push the args; unpacks the tuple
          add_def(n);
      else {
        assert nnn instanceof ConNode;
        for( TypeFld fld : ts )
          add_def(Node.con(fld._t));
      }
      _unpacked = true;     // Only do it once
      xval(); // Recompute value, this is not monotonic since replacing tuple with args
      GVN.add_work_new(this);// Revisit after unpacking
      return this;
    }

    Type tc = _val;
    if( !(tc instanceof TypeTuple) ) return null;
    TypeTuple tcall = (TypeTuple)tc;

    // Dead, do nothing
    if( tctl(tcall)!=Type.CTRL ) { // Dead control (NOT dead self-type, which happens if we do not resolve)
    //  if( (ctl() instanceof ConNode) ) return null;
    //   Kill all inputs with type-safe dead constants
    //  set_mem(Node.con(TypeMem.XMEM));
    //  set_dsp(Node.con(TypeFunPtr.GENERIC_FUNPTR.dual()));
    //  if( is_dead() ) return this;
    //  for( int i=ARG_IDX; i<_defs._len; i++ )
    //    set_def(i,Env.ANY);
    //  gvn.add_work_defs(this);
    //  return set_def(0,Env.XCTRL,gvn);
      throw unimpl();
    }

    // Have some sane function choices?
    TypeFunPtr tfp  = ttfp(tcall);
    BitsFun fidxs = tfp.fidxs();
    if( fidxs==BitsFun.EMPTY ) // TODO: zap function to empty function constant
      return null;             // Zero choices

    // Try to resolve to single-target
    Node fdx = fdx();
    if( fdx instanceof FreshNode fresh ) fdx = fresh.id();
    if( fdx instanceof UnresolvedNode unr ) {
      Node fdx2 = unr.resolve_node(tcall._ts);
      if( fdx2!=null )
        return set_fdx(fdx2);
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
    if( !is_keep() && err(true)==null && cepi!=null && cepi.is_all_wired() ) {
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
      GVN.add_reduce(cepi);
    GVN.add_flow(mem()); // Dead pointer args reduced to ANY, so mem() liveness lifts
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
      //for( int i=1; i<mem._defs._len; i++ )
      //  if( mem.in(i) instanceof MrgProjNode ) {
      //    // TODO: Renable this.  Requires escs-into-calls
      //    //Node x = _ideal_grow((MrgProjNode)mem.in(i),cepim,cepid,escs,i);
      //    //if( x!=null ) return x;
      //    return null;
      //  }
      throw unimpl();
    }
    return null;
  }

  //// Check for a Call/New that can either bypass or be placed in parallel
  //private Node _ideal_grow(MrgProjNode mem, ProjNode cepim, ProjNode cepid, BitsAlias escs, int i) {
  //  // No alias overlaps
  //  int alias = mem.nnn()._alias;
  //  if( escs.test_recur(alias) ) return null;
  //  // No other readers or writers.  Expect the Call (or Join)
  //  if( mem._uses._len>2 ) return null;
  //  // If call returns same as new (via recursion), cannot split, but CAN swap.
  //  TypeMem tmcepi = (TypeMem) cepim._val;
  //  BitsAlias esc_out = CallEpiNode.esc_out(tmcepi,cepid==null ? Type.XNIL : cepid._val);
  //  BitsAlias escs2 = escs.meet(esc_out);
  //  Node jn = mem();
  //  if( !escs2.is_empty() && !esc_out.test_recur(alias) ) { // No return conflict, so parallelize memory
  //    if( jn==mem )             // Bare Call/New; add a Split/Join.
  //      return MemSplitNode.insert_split(cepim,escs2,this,mem,mem);
  //    return null; // TODO: allow Call to move into existing JOIN
  //  } else {                    // Else move New below Call.
  //    if( jn!=mem ) {           // Move New below Join
  //      Node pre = mem.mem();
  //      jn.set_def(i,pre);
  //      mem.set_def(MEM_IDX,jn);
  //      set_mem(mem);
  //      Env.GVN.add_unuse(jn);
  //      Env.GVN.add_unuse(mem);
  //    }
  //    return swap_new(cepim,mem); // Move New below Call
  //  }
  //}

  //// Swap a New and a Call, when we cannot use a Split/Join.
  //private Node swap_new(Node cepim, MrgProjNode mrg ) {
  //  cepim.keep();
  //  cepim.insert(mrg);
  //  set_def(1,mrg.mem());
  //  mrg.set_def(1,cepim.unkeep());
  //  Env.GVN.revalive(mrg);
  //  Env.GVN.add_flow_uses(mrg);
  //  Env.GVN.add_flow(this);
  //  Env.GVN.add_flow(cepim.in(0));
  //  return this;
  //}

  // Pass thru all inputs directly - just a direct gather/scatter.  The gather
  // enforces SESE which in turn allows more precise memory and aliasing.  The
  // full scatter lets users decide the meaning; e.g. wired FunNodes will take
  // the full arg set but if the call is not reachable the FunNode will not
  // merge from that path.  Result tuple type:
  @Override public Type value() {
    if( _is_copy ) return _val; // Freeze until unwind
    // Pinch to XCTRL/CTRL
    Type ctl = ctl()._val;
    if( ctl != Type.CTRL ) return ctl.oob();
    // Function pointer.
    Node fdx = fdx();
    if( !(fdx._val instanceof TypeFunPtr tfx) ) return fdx._val.oob();
    // Not a memory to the call?
    Type mem = mem()==null ? TypeMem.ANYMEM : mem()._val;
    TypeMem tmem = mem instanceof TypeMem ? (TypeMem)mem : mem.oob(TypeMem.ALLMEM);

    // Result type includes a type-per-input
    final Type[] ts = Types.get(_defs._len+1/*+1 tescs turned off*/);
    ts[CTL_IDX] = Type.CTRL;
    ts[MEM_IDX] = tmem;         // Memory into the callee, not caller

    // Copy args for called functions.  FIDX is already refined.
    // Also gather all aliases from all args.
    ts[DSP_IDX] = tfx.dsp();
    for( int i=ARG_IDX; i<nargs(); i++ )
      ts[i] = arg(i)==null ? TypeNil.XSCALAR : arg(i)._val;
    ts[_defs._len] = tfx;
    // Resolve if possible, based on argument types and formals
    ts[_defs._len] = UnresolvedNode.resolve_value(ts);
    return TypeTuple.make(ts);
  }

  @Override public void add_flow_extra(Type old) {
    if( old==Type.ANY || _val==Type.ANY ||
        (old instanceof TypeTuple && ttfp(old).above_center()) )
      add_flow_defs();      // Args can be more-alive or more-dead
    // If Call flips to being in-error, all incoming args forced live/escape
     if( err(true)!=null )
      for( Node def : _defs )
        if( def!=null )
          GVN.add_flow(def);
  }

  @Override public void add_flow_def_extra(Node chg) {
    // Projections live after a call alter liveness of incoming args
    if( chg instanceof ProjNode proj && proj._idx < len())
      GVN.add_flow(in(proj._idx));
  }

  @Override public void add_flow_use_extra(Node chg) {
    CallEpiNode cepi = cepi();
    if( chg == fdx() ) {           // FIDX falls to sane from too-high
      add_flow_defs();             // All args become alive
      if( cepi!=null ) {
        GVN.add_work_new (cepi); // FDX gets stable, might wire, might unify_lift
        GVN.add_flow_defs(cepi); // Wired Rets might no longer be alive (might unwire)
      }
    } else if( chg == mem() ) {
      //if( cepi != null ) Env.GVN.add_flow(cepi);
    } else {                    // Args lifted, may resolve
      if( fdx() instanceof UnresolvedNode )
        GVN.add_reduce(this);
    }
  }

  @Override public Type live_use(Node def) {
    Type tcall = _val;
    if( !(tcall instanceof TypeTuple) ) // Call is has no value (yet)?
      return tcall.oob();
    if( is_keep()  ) return Type.ALL; // Still under construction, all alive
    if( def==ctl() ) return Type.ALL;
    if( def==mem() ) return _live;

    CallEpiNode cepi = cepi();
    if( def==fdx() ) {          // Function argument
      TypeFunPtr tfp = ttfp(tcall);
      BitsFun fidxs = tfp.fidxs();
      // If using a specific FunPtr and its in the resolved set, test more precisely
      RetNode ret;
      if( def instanceof FunPtrNode fptr &&  // Have a FunPtr
          (ret=fptr.ret())!=null &&          // Well-structured function
          !fidxs.test_recur(ret._fidx) )     // FIDX directly not used
        //return TypeMem.DEAD;                 // Not in the fidx set.
        throw unimpl();    // premature optimization?
      // Otherwise, the FIDX is alive.  Check the display.
      ProjNode dsp = ProjNode.proj(this,DSP_IDX);
      return ((!_is_copy && !cepi.is_all_wired()) || // Unwired calls remain, dsp could be alive yet
              (dsp!=null && dsp._live==Type.ALL)) ? Type.ALL : TypeFunPtr.GENERIC_FUNPTR;
    }

    // Check that all fidxs are wired; an unwired fidx might be in-error,
    // and we want the argument alive for errors.  This is a value turn-
    // around point (high fidxs need to fall)
    if( !_is_copy && !cepi.is_all_wired() ) return Type.ALL;
    // All wired, the arg is dead if the matching projection is dead
    int argn = _defs.find(def);
    ProjNode proj = ProjNode.proj(this, argn);
    return proj == null ? Type.ANY : proj._live; // Pass through live
  }

  @Override public boolean has_tvar() { return false; }

  // Unify ProjNodes with the Call arguments directly.
  @Override public boolean unify_proj( ProjNode proj, boolean test ) {
    TV3 tvp = proj.tvar();     // Projection tvar
    TV3 tv3 = tvar(proj._idx); // Input tvar matching projection
    if( proj._idx!=DSP_IDX )
      return tvp.unify(tv3,test); // Unify with Call arguments
    //// Specifically for the function/display, only unify on the display part.
    //if( tv3.is_fun() ) {        // Expecting the call input to be a function
    //  TV3 tdsp = tv3.arg("2");  // Unify against the function display
    //  return tdsp != null && tvp.unify(tdsp,test);
    //}
    //tv3.push_dep(proj);         // Proj will unify once tv3 becomes a fun
    //return false;
    throw unimpl();
  }

  @Override public ErrMsg err( boolean fast ) {
    // Expect a function pointer
    TypeFunPtr tfp = ttfp(_val);
    if( tfp.is_full() )
      return fast ? ErrMsg.FAST : ErrMsg.unresolved(_badargs[0],"A function is being called, but "+fdx()._val+" is not a function");

    BitsFun fidxs = tfp.fidxs();
    if( fidxs.above_center() ) return null; // Not resolved (yet)
    if( fidxs.is_empty() ) // This is an unresolved call
      throw unimpl();

    // bad-arg-count
    if( tfp.nargs() != nargs() ) {
      if( fast ) return ErrMsg.FAST;
      RetNode ret = RetNode.get(tfp.fidxs());
      return ErrMsg.syntax(_badargs[0],err_arg_cnt(ret.fun()._name,tfp));
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
          RetNode ret = RetNode.get(kid);
          if( ret==null ) continue;
          FunNode fun = ret.fun();
          ParmNode parm = fun.parm(j);
          if( parm==null ) continue;   // Formal is dead
          Type formal = parm._t;
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
  public String err_arg_cnt(String fname, TypeFunPtr tfp) {
    return "Passing "+(nargs()-DSP_IDX)+" arguments to "+fname+" which takes "+(tfp.nargs()-DSP_IDX)+" arguments";
  }

  public CallEpiNode cepi() {
    for( Node xcepi : _uses )    // Find CallEpi for bypass aliases
      if( xcepi instanceof CallEpiNode cepi )
        return cepi;
    return null;
  }

  @Override public Node is_copy(int idx) {
    if( !_is_copy ) return null;
    if( _val==Type.ANY ) return Env.ANY;
    if( idx!=DSP_IDX ) return in(idx);
    if( fdx() instanceof FunPtrNode fptr ) {
      GVN.add_flow(fptr);   // Probably goes unused
      return fptr.display();
    }
    return new FP2DSPNode(fdx()).init();
  }
  void set_rpc(int rpc) { unelock(); _rpc=rpc; } // Unlock before changing hash
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode call) ) return false;
    return _rpc==call._rpc;
  }
  public Node[] parms() {
    return _defs._len>= DSP_IDX ? Arrays.copyOf(_defs._es,_defs._len-1) : new Node[0]; // All defs, except the FIDX.
  }
}
