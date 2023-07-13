package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVErr;
import com.cliffc.aa.tvar.TVLambda;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.Env.GVN;

// Call/apply node.
//
// Control is not required for an apply but inlining the function body will
// require it; slot 0 is for Control.  Slot 1 is function memory, slot 2 the
// display; slot 3 is a Node typed as a TypeFunPtr; can be a FunPtrNode, or
// e.g. a Phi or a Load.  Slots 3+ are for other args.
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
  private final int _reset0_rpc; // Reset, if PrimNode rpcs split
  boolean _unpacked;        // One-shot flag; call site allows unpacking a tuple
  boolean _is_copy;         // One-shot flag; Call will collapse
  // Example: call(arg1,arg2)
  // _badargs[0] points to the opening paren.
  // _badargs[1] points to the start of arg1, same for arg2, etc.
  Parse[] _badargs;         // Errors for e.g. wrong arg counts or incompatible args; one error point per arg.

  public CallNode( boolean unpacked, Parse[] badargs, Node... defs ) {
    super(OP_CALL,defs);
    _rpc = BitsRPC.new_rpc(BitsRPC.ALLX); // Unique call-site index
    _reset0_rpc = _rpc;
    _unpacked=unpacked;         // Arguments are typically packed into a tuple and need unpacking, but not always
    _badargs = badargs;
    _live=RootNode.def_mem(null);
  }

  @Override public String xstr() { return (_is_copy ? "CopyCall" : (is_dead() ? "Xall" : "Call")); } // Self short name
  String  str() { return xstr(); }       // Inline short name
  @Override void walk_reset0() { set_rpc(_reset0_rpc); super.walk_reset0(); }
  @Override boolean is_CFG() { return !_is_copy; }
  @Override public boolean is_mem() { return true; }

  // Number of actual arguments, including closure/display at DSP_IDX.
  int nargs() { return _defs._len-1; }
  // Call arguments:
  // 0 - Control.  If XCTRL, call is not reached.
  // 1 - Memory.  This is memory into the call and also arg#0
  // 2 - Display; the first argument.
  // 3+  Other "normal" arguments, numbered#ARG_IDX and up.
  // N - Last input is the function.
  public Node ctl() { return in(CTL_IDX); }
  public Node mem() { return in(MEM_IDX); }
  public Node dsp() { return in(DSP_IDX); } // Display
  public Node fdx() { return in(nargs()); } // Function
  Node arg ( int x ) { assert x>=0; return _defs.at(x); }
  // Set arguments
  void set_xmem() { set_def(MEM_IDX, Env.ANY); }
  void set_xarg(int idx) { assert idx>=DSP_IDX && idx <nargs();  set_def(idx, Env.ANY); }
  void set_fdx(Node fun) {
    assert fun._val instanceof TypeFunPtr;
    set_def(nargs(), fun);
    xval();                     // Recompute value
  }

  // Add a bunch of utilities for breaking down a Call.value tuple:
  // takes a Type, upcasts to tuple, & slices by name.
  // ts[0] == in(0) == ctl() == Ctrl
  // ts[1] == in(1) == mem() == Mem into the callee = mem()
  // ts[2] == in(2) == dsp() == Display pointer
  // ts[3] == in(3) == arg(3)
  // ts[4] == in(4) == arg(4)
  // ....
  // ts[_defs._len]   = Function, as a TFP
  static Type    targ( TypeTuple tcall, int i ) { return tcall._ts[i]; }
  static Type    tctl( TypeTuple tcall ) { return targ(tcall,CTL_IDX); }
  static TypeMem emem( TypeTuple tcall ) { return emem(tcall._ts); }
  static TypeMem emem( Type[] ts ) { return (TypeMem)ts[MEM_IDX]; } // callee memory passed into function
  // No-check must-be-correct get TFP
  static public TypeFunPtr ttfp( Type t ) {
    return (TypeFunPtr)((t instanceof TypeTuple tcall)
                        ? tcall._ts[tcall.len()-1]
                        : t.oob(TypeFunPtr.GENERIC_FUNPTR));
  }
  TypeFunPtr tfp() { return ttfp(_val); }

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
    if( is_prim() ) return null;
    Node cc = fold_ccopy();
    if( cc != null ) return cc;
    if( _is_copy) return null;

    // When do I do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked &&           // Not yet unpacked a tuple
        val(DSP_IDX) instanceof TypeStruct ts && // An arg collection
        ts.is_tup() ) {                          // A tuple
      // Find a tuple being passed in directly; unpack
      Node fun = pop(); // Pop off the function
      Node nnn = pop(); // Pop off the tuple
      if( nnn instanceof StructNode )
        for( Node n : nnn._defs ) // Push the args; unpacks the tuple
          add_def(n);
      else {
        assert nnn instanceof ConNode;
        for( TypeFld fld : ts )
          add_def(Node.con(fld._t));
      }
      add_def(fun);             // Function at end
      _unpacked = true;         // Only do it once
      xval(); // Recompute value, this is not monotonic since replacing tuple with args
      GVN.add_work_new(this);// Revisit after unpacking
      fdx().add_flow();      // Also, fcn/dsp liveness changes
      return this;
    }

    Type tc = _val;
    if( !(tc instanceof TypeTuple tcall) ) return null;

    // Dead, do nothing
    if( tctl(tcall)!=Type.CTRL ) { // Dead control (NOT dead self-type, which happens if we do not resolve)
      if( (ctl() instanceof ConNode) ) return null;
      // Kill all inputs with type-safe dead constants
      set_xmem();
      for( int i=ARG_IDX; i<_defs._len; i++ )
        set_def(i,Env.ANY);
      CallEpiNode cepi = cepi();
      if( cepi==null ) {
        while( _uses._len>0 ) {
          Node use = _uses.last();
          assert use instanceof FunNode;
          use.remove(use._defs.find(this));
        }
      }
      return set_def(0,Env.XCTRL);
    }

    // Have some sane function choices?
    TypeFunPtr tfp  = ttfp(tcall);
    BitsFun fidxs = tfp.fidxs();
    if( fidxs==BitsFun.EMPTY ) // TODO: zap function to empty function constant
      return null;             // Zero choices

    // Wire valid targets.
    CallEpiNode cepi = cepi();
    if( cepi!=null && cepi.CG_wire() )
      return Env.GVN.add_reduce(this); // Re-run for other progress

    // Check for dead args and trim; must be after all wiring is done because
    // unknown call targets can appear during GCP and use the args.  After GCP,
    // still must verify all called functions have the arg as dead, because
    // alive args still need to resolve.
    if( cepi!=null && ttfp(tcall)._fidxs != BitsFun.NALL && !is_keep() && err(true)==null && cepi.is_CG(true) ) {
      // 1 bit for each argument, used to track arg usage
      int abits = 0;
      for( int i=DSP_IDX; i<nargs(); i++ ) if( in(i)!=Env.ANY ) abits |= (1<<i);
      // Find arg uses
      if( abits!=0 )
        for( Node use : _uses ) {
          if( use instanceof CallEpiNode ) continue;
          if( use instanceof FunNode fun ) {
            for( Node fuse : fun._uses )
              if( fuse instanceof ParmNode parm ) {
                abits &= ~(1<<parm._idx); // Arg is used
                parm.deps_add(this);      // Arg dies, then this call improves
              }
          } else abits=0; // Root uses all
          if( abits==0 ) break;
        }
      // If some args are unused, set to ANY
      if( abits!=0 ) {
        for( int i=DSP_IDX; i<nargs(); i++ )
          if( (abits & (1<<i))!=0 )
            set_xarg(i);
        return this;
      }
    }
    return null;
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
    if( cepim == null ) return null;
    if( !(cepim._val instanceof TypeMem tmcepi) ) return null;
    if( !mem._val.isa(tmcepi) ) return null; // Call entry stale relative to exit
    //// Check for prior Join
    if( mem instanceof MemJoinNode ) {
      if( !mem.check_solo_mem_writer(this) )
        return null;
      throw unimpl();
    }
    return null;
  }

  // Pass thru all inputs directly - just a direct gather/scatter.  The gather
  // enforces SESE which in turn allows more precise memory and aliasing.  The
  // full scatter lets users decide the meaning; e.g. wired FunNodes will take
  // the full arg set but if the call is not reachable the FunNode will not
  // merge from that path.  Result tuple type:
  @Override public Type value() {
    if( _is_copy ) return _val; // Freeze until unwind

    // CallEpi is dead from below and not a copy - this whole path is dead.
    // Lift to ANY and let DCE remove final uses.  Complex test is to avoid
    // killing a Call under construction during Parse: will have no uses, no
    // Keep and no cepi (for a tiny short time).
    if( val(0)==Type.XCTRL || val(0)==Type.ANY ) return Type.ANY;

    // Result type includes a type-per-input, plus one for the function
    final Type[] ts = Types.get(_defs._len);
    ts[CTL_IDX] = ctl()._val.oob(Type.CTRL);
    // Not a memory to the call?
    Type mem = mem()==null ? TypeMem.ANYMEM : mem()._val;
    TypeMem tmem = mem instanceof TypeMem ? (TypeMem)mem : mem.oob(TypeMem.ALLMEM);
    ts[MEM_IDX] = tmem;         // Memory into the callee, not caller

    // Function pointer.
    Node fdx = fdx();
    TypeFunPtr tfx = switch( fdx._val ) {
    case TypeFunPtr tfx2 -> tfx2;
    case TypeNil tn -> {
      int nargs = Combo.pre() ? 1
        : (switch( fdx.tvar() ) {
          case TVLambda lam -> lam.nargs();
          case TVErr err -> err.as_lambda().nargs();
          default -> -1;
          });
      yield TypeFunPtr.make(tn.above_center(),tn._fidxs,nargs,tn.oob(),tn.oob());
    }
    default -> fdx._val.oob(TypeFunPtr.GENERIC_FUNPTR);
    };
    // Copy args for called functions.  FIDX is already refined.
    // Also gather all aliases from all args.
    for( int i=DSP_IDX; i<nargs(); i++ )
      ts[i] = arg(i)==null ? TypeNil.XSCALAR : arg(i)._val;
    ts[_defs._len-1] = tfx;

    return TypeTuple.make(ts);
  }

  static final Type FP_LIVE = TypeStruct.UNUSED.add_fldx(TypeFld.make("fp",Type.ALL));
  @Override public Type live_use( int i ) {
    Node def = in(i);
    if( _is_copy ) return def._live;
    boolean is_keep = is_keep();
    if( i==CTL_IDX ) return Type.ALL;
    if( i==MEM_IDX ) return is_keep || _live==Type.ALL ? RootNode.def_mem(def) : _live;
    if( i==nargs() ) return _unpacked ? FP_LIVE : Type.ALL;
    if( !_unpacked ) return TypeStruct.ISUSED;
    if( is_keep  )   return Type.ALL; // Still under construction, all alive

    // Unresolved calls need their inputs alive, so those now-live inputs unify
    // and can be used to resolve.  This gets to a key observation: cannot use
    // dead inputs to resolve a call!  The call input *must* have some uses
    // which distinguish which function to call.  Cannot flip this during
    // Combo, as will break monotonicity.
    //
    // Example:
    // N482: Fresh  N___ VAL=3                 , LIVE=ANY     , HMT=    V504            // Since not live, no unify
    // N479: ._     N251 VAL={pair of hi funcs}, LIVE=FP-alone, HMT={ 2 V504 -> +V460 } // Since V504 is a leaf, does not pick between FP or INT adds so unresolved
    // N483: Call   Nctl Nmem _2_ N482 N479 VAL={Ctrl,Mem,2,3,pair-o-hi-funcs}, LIVE=[[ALIVE_no_mem]]
    //
    // Here Call is alive, but not wired... so if I leave the args not-alive:
    // THEN Fresh is not alive and does not unify V504 and Int:3
    // THEN V504 in the Resolving N479 Field is Leaf not Int, and does not resolve.
    if( i>DSP_IDX && !LIFTING ) return Type.ALL;

    // Check that all fidxs are wired.  If not wired, a future wired fidx might
    // use the call input.  Post-Combo, all is wired, but dead Calls might be
    // unwinding.
    if( val(0)==Type.XCTRL ) return Type.ANY;
    CallEpiNode cepi = cepi();
    if( cepi==null ) {
      deps_add(def);
      return Type.ALL.oob(Combo.post());
    }
    if( !cepi.is_CG(true) ) return Type.ALL; // Not fully wired, assume a worse user yet to come

    // Since wired, we can check all uses to see if this argument is alive.
    Type t = Type.ANY;
    for( Node use : _uses ) {
      // The 3 allowed types are CallEpi, Root and Fun
      if( use instanceof CallEpiNode ) continue;
      if( use instanceof RootNode ) return Type.ALL;
      FunNode fun = (FunNode)use;
      // Find argument getting liveness computed
      ParmNode parm = fun.parm(i);
      if( parm!=null ) {    // Parm is in use?
        parm.deps_add(def);
        t = t.meet(parm._live); // As alive as the using Parm
        if( t == Type.ALL ) return Type.ALL;
      }
    }
    return t;
  }


  @Override public boolean has_tvar() { return false; }

  // Unify ProjNodes with the Call arguments directly.
  @Override public boolean unify_proj( ProjNode proj, boolean test ) {
    TV3 tvp = proj.tvar();     // Projection tvar
    TV3 tv3 = tvar(proj._idx); // Input tvar matching projection
    if( proj._idx!=DSP_IDX )
      return tvp.unify(tv3,test); // Unify with Call arguments
    // Specifically for the function/display, only unify on the display part.
    if( tv3 instanceof TVLambda lam ) // Expecting the call input to be a function
      return lam.dsp().unify(tvp,test);
    return tv3.deps_add_deep(proj);    // Proj will unify once tv3 becomes a fun
  }

  @Override public ErrMsg err( boolean fast ) {
    // Expect a function pointer
    TypeFunPtr tfp = ttfp(_val);
    if( tfp.is_empty() )
      return fast ? ErrMsg.FAST : ErrMsg.unresolved(_badargs==null ? null : _badargs[0],"A function is being called, but "+fdx()._val+" is not a function");

    BitsFun fidxs = tfp.fidxs();
    if( fidxs.above_center() ) return null; // Not resolved (yet)
    if( fidxs==BitsFun.NALL ) return null;  // Unknown function

    // bad-arg-count
    if( tfp.nargs() != nargs() ) {
      if( fast ) return ErrMsg.FAST;
      RetNode ret = RetNode.get(tfp.fidxs());
      return ErrMsg.syntax(_badargs[0],err_arg_cnt(ret.funptr()._name,tfp));
    }

    // Now do an arg-check.  No more than 1 unresolved, so the error message is
    // more sensible.
    BitsFun.Tree<BitsFun> tree = fidxs.tree();
    for( int j=ARG_IDX; j<nargs(); j++ ) {
      Type actual = arg(j).sharptr(mem());
      Ary<Type> ts=null;
      for( int fidx : fidxs ) {
        if( fidx==0 ) continue;
        if( BitsFun.EXT.test_recur(fidx) ) continue; // External callers have args forced via H-M types elsewhere
        for( int kid=fidx; kid!=0; kid = tree.next_kid(fidx,kid) ) {
          RetNode ret = RetNode.get(kid);
          if( ret==null || ret.is_copy() ) continue;
          FunNode fun = ret.fun();
          ParmNode parm = fun.parm(j);
          if( parm==null ) continue;   // Formal is dead
          Type formal = parm._t;
          if( formal==TypeNil.SCALAR || actual.isa(formal) ) continue; // Actual is a formal
          if( fast ) return ErrMsg.FAST;     // Fail-fast
          if( ts==null ) ts = new Ary<>(new Type[1],0);
          if( ts.find(formal) == -1 ) // Dup filter
            ts.push(formal);          // Add broken type
        }
      }
      if( ts!=null )
        return ErrMsg.typerr2(_badargs[j-ARG_IDX+1],actual,ts.asAry());
    }

    return null;
  }
  public String err_arg_cnt(String fname, TypeFunPtr tfp) {
    return "Passing "+(nargs()-ARG_IDX)+" arguments to "+fname+" which takes "+(tfp.nargs()-ARG_IDX)+" arguments";
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
    return in(idx);
  }
  void set_rpc(int rpc) { unelock(); _rpc=rpc; } // Unlock before changing hash
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode call) ) return false;
    return _rpc==call._rpc;
  }
}
