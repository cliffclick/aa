package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.NonBlockingHashMap;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.BitSet;
import java.util.Map;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.*;

// FunNodes are lexically scoped.  During parsing/graph-gen a closure is
// allocated for local variables as a standard NewObj.  Local escape analysis
// is used to remove NewObjs that do not escape the local lifetime.  Scoped
// variables pass in their NewObj pointer just "as if" a normal struct.
//
// Function bodies are self-contained; they only take data in through ParmNodes
// and ConNodes, and only control through the Fun.  They only return values
// through the RetNode - including exposed lexically scoped uses.
//
// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// null, same as a C2 Region.  Args 1+ point to the callers control.  Before
// GCP/opto arg 1 points to SCP_0 as the generic unknown worse-case caller.
// This goes dead during GCP, the precise call-graph is discovered, and calls
// are directly wired to the FunNode as part of GCP.  After GCP the call-graph
// is known precisely and is explicit in the graph.
//
// FunNodes are finite in count and are unique densely numbered, see BitsFun.
// A single function number is generally called a 'fidx' and collections 'fidxs'.
//
// Pointing to the FunNode are ParmNodes which are also PhiNodes; one input
// path for each known caller.  Zero slot points to the FunNode.  Arg1 points
// to the generic unknown worse-case caller (a type-specific ConNode with
// worse-case legit bottom type).  ParmNodes merge all input path types (since
// they are a Phi), and the call "loses precision" for type inference there.
// Parm#1 and up (NOT the zero-slot but the zero idx) are the classic function
// arguments; Parm#-1 is for the RPC and Parm#0 is for memory.
//
// Ret points to the return control, memory, value and RPC, as well as the
// original Fun.  A FunPtr points to a RetNode, and a Call will use a FunPtr (or a
// merge of FunPtrs) to indicate which function it calls.  After a call-graph
// edge is discovered, the Call is "wired" to the Fun.  A CallEpi points to the
// RetNode, the Fun control points to a CProj to the Call, and each Parm points to
// a DProj (MProj) to the Call.  These direct edges allow direct data flow
// during gcp & iter.
//
// Memory both is and is-not treated special: the function body flows memory
// through from the initial Parm to the RetNode in the normal way.  However, the
// incoming memory argument is specifically trimmed by the Call to only those
// aliases used by the function body (either read or write), and the RetNode only
// returns those memories explicitly written.  All the other aliases are
// treated as "pass-through" and explicitly routed around the Fun/Ret by the
// Call/CallEpi pair.


public class FunNode extends Node {
  public String _name;      // Debug-only name
  public int _fidx;         // Unique number for this piece of code
  public int _nargs;        // Number of arguments

  private byte _cnt_size_inlines; // Count of size-based inlines; prevents infinite unrolling via inlining
  public static int _must_inline; // Used for asserts

  // Used to make the primitives at boot time.  Note the empty displays: in
  // theory Primitives should get the top-level primitives-display, but in
  // practice most primitives neither read nor write their own scope.
  public FunNode(PrimNode prim, String name) { this(name, prim._tfp.fidx(),prim._tfp.nargs()); }
  // Used to start an anonymous function in the Parser
  public FunNode(int nargs) { this(null, nargs); }
  // Used to forward-decl anon functions
  FunNode(String name) { this(name, 0); add_def(Env.SCP_0); }
  // Shared common constructor for Named type constructors
  FunNode(String name, int nargs ) { this(name, BitsFun.new_fidx(), nargs); }
  // Shared common constructor
  FunNode( String name, int fidx, int nargs ) {
    super(OP_FUN,(Node)null);
    _name = name;
    _fidx = fidx;
    _nargs = nargs;
  }
  public static void reset_to_init0() { _must_inline=0; }

  // Short self name
  @Override public String xstr() { return name(); }
  // Inline longer info
  @Override public String str() { return name(); }
  // Name from FunNode
  String name() { return name(true); }
  public String name(boolean debug) {
    String name = _name;
    if( name==null && !is_dead() ) {
      for( Node use : _uses )
        if( use instanceof RetNode ret )
          for( Node ruse : ret._uses )
            if( ruse instanceof FunPtrNode fptr )
              name = fptr._name;
    }
    if( debug ) name = name + "["+_fidx+"]"; // FIDX in debug
    return name;
  }

  // Debug only: make an attempt to bind name to a function
  public void bind( String tok ) {
    if( _name==null ) _name = tok;
    if( !_name.equals(tok) ) // Attempt to double-bind
      _name = _name+":"+tok;
  }

  // This function has disabled inlining
  public boolean noinline() {
    return in(0)==null && _name!=null && _name.startsWith("noinline");
  }

  // Never inline with a nested function
  @Override @NotNull public FunNode copy( boolean copy_edges) { throw unimpl(); }
  @Override boolean is_CFG() { return is_copy(0)==null; }

  public int nargs() { return _nargs; }

  // True if more unknown callers may appear on a Fun, Parm, Call, CallEpi, Ret.
  // One-shot transition from having unknown callers to not having.
  // At Combo, all callers are known and stay known: even Root is a known caller.
  private boolean _unknown_callers = true;
  public boolean unknown_callers( Node dep ) {
    if( _unknown_callers && dep!=null ) deps_add(dep);
    return _unknown_callers;
  }
  // Checks the unknown caller situation, and one-shot transits from having
  // unknown-callers to all-callers-known.
  public boolean set_unknown_callers() {
    if( !_unknown_callers || _unknown_callers() ) return false;
    _unknown_callers=false;   // One-shot transition
    deps_work_clear();        // Folks who depend on it get touched
    return true;              // Progress
  }

  private boolean _unknown_callers() {
    if( is_keep() || is_prim() ) return true; // Still alive
    if( is_copy(0)!=null ) return false;      // Copy collapsing
    // Can only track if we can follow all uses of FunPtr
    FunPtrNode fptr = fptr();
    if( fptr == null ) return false; // Need a funptr to have a new unknown caller
    if( all_uses_are_wired(fptr) ) return false;
    // TODO: No way to track unwired
    return Combo.pre();
  }

  private boolean all_uses_are_wired(FunPtrNode fptr) {
    for( Node use : fptr._uses ) {
      use.deps_add(this);
      if( !use_is_wired(fptr,use) )
        return false;
    }
    return true;
  }
  private boolean use_is_wired(FunPtrNode fptr, Node use) {
    if( use instanceof CallEpiNode ) return true; // Wired to a CEPI
    if( !(use instanceof CallNode call) ) return false; // Unknown use
    if( call.is_keep() ) return false; // Not wirable yet
    if( call._is_copy ) return false; // Mid-collapse
    for( int i=DSP_IDX; i<call.nargs(); i++ )
      if( call.in(i)==fptr )
        return false;           // Use as an arg
    assert call.fdx()==fptr;    // Used to directly call
    // CEPI should be wired to the fptr.
    return call.cepi()._defs.find(fptr.ret())!= -1;
  }

  @Override public Type value() {
    if( unknown_callers(this) ) return Type.CTRL;
    if( in(0)==this )           // is_copy
      return val(1).oob(Type.CTRL);
    for( int i=1; i<_defs._len; i++ ) {
      if( in(i)==this ) continue; // Ignore self-loop
      Type c = val(i);
      // Wired to either Call or Root, both with Tuple values.
      if( !(c instanceof TypeTuple ct ? ct.at(0) : c).above_center() ) return Type.CTRL;
    }
    return Type.XCTRL;
  }

  @Override public Node ideal_reduce( ) {
    if( in(0)==this && _uses._len==1 ) return Env.ANY; // Kill lonely self cycle
    if( set_unknown_callers() ) return this;
    Node progress=null;
    for( int i=1; i<len(); i++ )
      if( val(i).above_center() )  Env.GVN.add_unuse(progress = del(i));
      else  in(i).deps_add(this);
    return progress==null ? null : this;
  }

  @Override public Type live_use( int i ) {
    if( in(0)==this ) return _live; // Dead self-copy
    Node def = in(i);
    if( def instanceof RootNode ) throw unimpl();
    if( def instanceof ConNode ) return Type.ANY; // Dead control path
    assert def.is_CFG();
    ParmNode pmem = parm(MEM_IDX);
    if( pmem==null ) return TypeMem.ANYMEM; // No mem parm, so pure function
    pmem.deps_add(def);
    if( !(pmem._live instanceof TypeMem mem) ) return Type.ANY;
    TypeMem mem2 = mem.remove(RootNode.KILL_ALIASES);
    return mem2;                // Pass through mem liveness
  }

  // ----
  // Graph rewriting via general inlining.  All other graph optimizations are
  // already done.
  public Node ideal_inline(boolean check_progress) {
    if( noinline() ) return null;
    assert is_copy(0)==null; // If a copy, should have already cleaned out before getting here

    // Every input path is wired to an output path
    RetNode ret = ret();
    if( ret==null ) return null;
    for( int i=1; i<_defs._len; i++ ) {
      if( in(i) instanceof CallNode call ) assert call.cepi().is_CG(true);
      else if( in(i) instanceof RootNode root ) assert root.is_CG(true);
      else return null;
    }

    // Look for appropriate type-specialize callers
    Ary<Node> body = find_body(ret);
    // Large code-expansion allowed; can inline for other reasons
    int path = split_size(body,parms()); // Forcible size-splitting first path
    if( path == -1 ) return null;
    if( !is_prim() ) {
      if( _cnt_size_inlines >= 6 ) return null;
      _cnt_size_inlines++; // Disallow infinite size-inlining of recursive non-primitives
    }
    CallNode call = (CallNode)in(path);
    body.add(fptr());

    assert _must_inline==0; // Failed to inline a prior inline?
    if( path > 0 ) _must_inline = call._uid;
    assert !check_progress;     // Not expecting progress

    // --------------
    // Split the callers according to the new 'fun'.
    FunNode fun = make_new_fun(ret, path);
    split_callers(ret,fun,body,path);
    boolean x = fun.set_unknown_callers(); assert x; // Will be false now, so makes progress
    assert Env.ROOT.more_work(true)==0; // Initial conditions are correct
    //assert Env.ROOT.no_more_ideal();
    return this;
  }

  // Return the function body.
  private Ary<Node> find_body( RetNode ret ) {
    // Find the function body.  Do a forwards walk first, stopping at the
    // obvious function exit.  If function does not expose its display then
    // this is the complete function body with nothing extra walked.  If it has
    // a nested function or returns a nested function then its display is may
    // be reached by loads & stores from outside the function.
    //
    // Then do a backwards walk, intersecting with the forwards walk.  A
    // backwards walk will find upwards-exposed values, typically constants and
    // display references - could be a lot of them.  Minor opt to do the
    // forward walk first.
    VBitSet freached = new VBitSet(); // Forwards reached
    Ary<Node> work = new Ary<>(new Node[1],0);
    work.add(this);             // Prime worklist
    while( !work.isEmpty() ) {  // While have work
      Node n = work.pop();      // Get work
      int op = n._op;           // opcode
      if( op == OP_FUN  && n       != this ) continue; // Call to other function, not part of inlining
      if( op == OP_PARM && n.in(0) != this ) continue; // Arg  to other function, not part of inlining
      if( op == OP_ROOT ) continue; // Escaped global function
      if( op == OP_RET && n != ret ) continue; // Return (of other function)
      // OP_FUNPTR: Can be reached from an internal NewObjNode/display, or
      // following the local Return.  The local FunPtrs are added below.
      // Adding the reached FunPtrs here clones them, making new FunPtrs using
      // either the old or new display.
      if( freached.tset(n._uid) ) continue; // Already visited?
      if( op == OP_RET ) continue;          // End of this function
      if( n instanceof ProjNode && n.in(0) instanceof CallNode ) continue; // Wired call; all projs lead to other functions
      work.addAll(n._uses);   // Visit all uses
    }

    // Backwards walk, trimmed to reachable from forwards
    VBitSet breached = new VBitSet(); // Backwards and forwards reached
    Ary<Node> body = new Ary<>(new Node[1],0);
    work.add(ret);
    while( !work.isEmpty() ) {  // While have work
      Node n = work.pop();      // Get work
      if( n==null ) continue;   // Defs can be null
      // As a special case for H-M, always clone uses of nil constants.
      // These need private H-M variables to support polymorphic nil-typing.
      if( n instanceof ConNode && ((ConNode)n)._t==TypeNil.XNIL ) freached.tset(n._uid);
      if( !freached.get (n._uid) ) continue; // Not reached from fcn top
      if(  breached.tset(n._uid) ) continue; // Already visited?
      body.push(n);                          // Part of body
      work.addAll(n._defs);                  // Visit all defs
      if( n.is_multi_head() )                // Multi-head?
        work.addAll(n._uses);                // All uses are ALSO part, even if not reachable in this fcn
    }
    return body;
  }

  // Split a single-use copy (e.g. fully inline) if the function is "small
  // enough".  Include anything with just a handful of primitives, or a single
  // call, possible with a single if.  Disallow functions returning a new
  // allocation & making other (possibly recursive) calls: the recursive-loop
  // prevents lifting the allocations from the default parent to either child
  // without a full GCP pass - which means we split_size but then cannot inline
  // in CEPI because the Ret memory type will never lift to the default memory.
  private int split_size( Ary<Node> body, Node[] parms ) {
    if( _defs._len <= 1 ) return -1; // No need to split callers if only 1
    boolean self_recursive=false;

    // Count function body size.  Requires walking the function body and
    // counting opcodes.  Some opcodes are ignored, because they manage
    // dependencies but make no code.
    int call_indirect=0; // Count of calls to e.g. loads/args/parms
    int[] cnts = new int[OP_MAX];
    for( Node n : body ) {
      int op = n._op;           // opcode
      if( n instanceof CallNode call ) {     // Call-of-primitive?
        Node fdx = call.fdx();
        if( fdx._val instanceof TypeFunPtr tfp ) { // Calling an unknown function, await GCP
          if( tfp.test(_fidx) ) self_recursive = true; // May be self-recursive
        }

          // if( false) {
        //  fdx.deps_add(this);
        //  return -1;
        //}
        //if( tfp.test(_fidx) ) self_recursive = true; // May be self-recursive
        //if( fdx instanceof FunPtrNode fpn ) {
        //  if( fpn.ret().rez() instanceof PrimNode )
        //    op = OP_PRIM;       // Treat as primitive for inlining purposes
        //} else
        //  call_indirect++;
      }
      cnts[op]++;               // Histogram ops
    }
    assert cnts[OP_FUN]==1 && cnts[OP_RET]==1;
    assert cnts[OP_SCOPE]==0;
    assert cnts[OP_REGION] <= cnts[OP_IF];

    // Specifically ignoring constants, parms, phis, RPCs, types,
    // unresolved, and casts.  These all track & control values, but actually
    // do not generate any code.
    if( cnts[OP_CALL] > 2 || // Careful inlining more calls; leads to exponential growth
        cnts[OP_LOAD] > 4 ||
        cnts[OP_STORE]> 2 ||
        cnts[OP_PRIM] > 6 ||   // Allow small-ish primitive counts to inline
        cnts[OP_NEW]>2 ||      // Display and return is OK
        (cnts[OP_NEW]>1 && self_recursive)
        //|| call_indirect > 0
        )
      return -1;

    //if( self_recursive ) return -1; // Await GCP & call-graph discovery before inlining self-recursive functions

    // Pick which input to inline.  Only based on having some constant inputs
    // right now.
    int m=-1, mncons = -1;
    for( int i=1; i<_defs._len; i++ ) {
      if( !(in(i) instanceof CallNode call) || // Not well-formed (or Root)
          call.nargs() != nargs()  ||          // Will not inline
          call._val == Type.ALL ) continue;    // Otherwise in-error
      TypeFunPtr tfp = CallNode.ttfp(call._val);
      int fidx = tfp.fidxs().abit();
      if( fidx < 0 || BitsFun.is_parent(fidx) ) continue;    // Call must only target one fcn
      if( self_recursive && body.find(call)!=-1 ) continue; // Self-recursive; amounts to unrolling
      int ncon=0;
      // Count constant inputs on non-error paths
      for( int j=DSP_IDX; j<parms.length; j++ ) {
        ParmNode parm = (ParmNode)parms[j];
        if( parm != null ) {    // Some can be dead
          Type actual = call.val(j);
          Type formal = parm._t;
          if( !actual.isa(formal) ) // Path is in-error?
            { ncon = -2; break; }   // This path is in-error, cannot inline even if small & constants
          if( actual.is_con() ) ncon++; // Count constants along each path
        }
      }
      if( ncon > mncons )
        { mncons = ncon; m = i; } // Path with the most constants
    }
    if( m == -1 )               // No paths are not in-error? (All paths have an error-parm)
      return -1;                // No inline

    if( cnts[OP_IF] > 1+mncons) // Allow some trivial filtering to inline
      return -1;

    return m;                   // Return path to split on
  }

  private FunNode make_new_fun(RetNode ret, int path) {
    // Make a prototype new function header split from the original.
    int oldfidx = _fidx;
    FunNode fun = new FunNode(_name, BitsFun.new_fidx(path==-1 ? oldfidx : BitsFun.parent(oldfidx)),_nargs);
    fun.pop();                  // Remove null added by RegionNode, will be added later
    fun._val = Type.CTRL;

    // If type-splitting renumber the original as well; the original _fidx is
    // now a *class* of 2 fidxs.  Each FunNode fidx is only ever a constant, so
    // the original Fun becomes the other child fidx.  If size-splitting there
    // are no callers of the new fidx other than the call site.
    if( path == -1 ) {
      int newfidx = _fidx = BitsFun.new_fidx(oldfidx);
      ret.set_fidx(newfidx);      // Renumber in the old RetNode
      // Right now, force the type upgrade on old_fptr.  old_fptr carries the old
      // parent FIDX and is on the worklist.  Eventually, it comes off and the
      // value() call lifts to the child fidx.  Meanwhile, its value can be used
      // to wire a size-split to itself (e.g. fib()), which defeats the purpose
      // of a size-split (single caller only, so inlines).
      for( Node old_fptr : ret._uses )
        if( old_fptr instanceof FunPtrNode ) // Can be many old funptrs with different displays
          old_fptr.xval();                   // Upgrade FIDX
    }
    Env.GVN.add_flow(ret);
    Env.GVN.add_flow(this);
    Env.GVN.add_flow_uses(this);
    Env.GVN.add_reduce(fun);
    return fun;
  }

  // ---------------------------------------------------------------------------
  // Clone the function body, and split the callers of 'this' into 2 sets; one
  // for the old and one for the new body.  The new function may have a more
  // refined signature, and perhaps no unknown callers.
  //
  // Wired calls: unwire all calls *to* this function, including self-calls.
  // Clone the function; wire calls *from* the clone same as the original.
  // Then rewire all calls that were unwired; for a path-split rewire left-or-right by path.
  private void split_callers( RetNode oldret, FunNode fun, Ary<Node> body, int path ) {
    assert path >= 0;           // TODO: Re-enable type splitting
    // Unwire this function and collect unwired calls.  Leave a Root caller, if any.
    CallNode path_call = (CallNode)in(path);
    Ary<CallEpiNode> unwireds = new Ary<>(new CallEpiNode[1],0);
    while( _defs._len > 1 ) {   // For all paths except Root
      CallNode call = (CallNode)pop(); // TODO: Root
      CallEpiNode cepi = call.cepi();
      cepi.del(cepi._defs.find(oldret));
      unwireds.add(cepi);
      Env.GVN.add_reduce(cepi); // Visit for inlining later
      assert cepi.is_CG(false);
    }

    // Map from old to cloned function body
    NonBlockingHashMap<Node,Node> map = new NonBlockingHashMap<>();
    // Collect aliases that are cloning.
    BitSet aliases = new BitSet();
    // Clone the function body
    map.put(this,fun);
    for( Node n : body ) {
      if( n==this ) continue;     // Already cloned the FunNode
      int old_alias = n instanceof NewNode nnn ? nnn._alias : -1;
      Node c = n.copy(false);     // Make a blank copy with no edges
      map.put(n,c);               // Map from old to new
      if( old_alias != -1 )       // Was a NewNode?
        aliases.set(old_alias);   // Record old alias before copy/split
      // Slightly better error message when cloning constructors
      if( n instanceof MemPrimNode mpn )
        //mpn._badargs = path_call._badargs;
        throw unimpl();
    }

    // Fill in edges.  New Nodes point to New instead of Old; everybody
    // shares old nodes not in the function (and not cloned).
    for( Node n : map.keySet() ) {
      Node c = map.get(n);
      assert c._defs._len==0;
      for( Node def : n._defs ) {
        Node newdef = def==null ? null : map.get(def);// Map old to new
        c.add_def(newdef==null ? def : newdef);
      }
    }
    // Update FIDX in new code
    RetNode newret = (RetNode)map.get(oldret);
    newret.set_fidx(fun._fidx);

    // Hardwire the path call to the clone
    Node old_funptr = fptr();
    Node new_funptr = map.get(old_funptr);
    new_funptr.xval();
    new_funptr.insert(old_funptr); // Make cloned recursive calls, call the old version not the new version
    path_call.set_fdx(new_funptr); // Force new_funptr, will re-wire later

    // For all aliases split in this pass, update in-node both old and new.
    // This changes their hash, and afterwards the keys cannot be looked up.
    for( Map.Entry<Node,Node> e : map.entrySet() )
      if( e.getKey() instanceof MemSplitNode memsplit )
        //memsplit.split_alias(e.getValue(),aliases);
        throw unimpl();

    // Rewire all unwired calls.
    for( CallEpiNode cepi : unwireds ) {
      // Load before changing edges (and hash)
      CallEpiNode cepi2 = (CallEpiNode)map.get(cepi);
      boolean progress = cepi.CG_wire();
      assert progress;
      // Check for an unwired call in the body - this musta been a recursive
      // self-call.
      if( cepi2!=null && cepi2.call()!=path_call ) {
         // wire the clone, same as the original was wired, so the clone as as
         // a peel of the original recursive loop.
         cepi2.call().set_fdx(cepi.call().fdx());
         cepi2.CG_wire();
      }
    }

    // Look for wired new not-recursive CallEpis; these will have an outgoing
    // edge to some other RetNode, but the Call will not be wired.  Wire.
    for( Node nn : map.values() ) {
      if( nn instanceof CallEpiNode ncepi ) {
        CallNode ncall = ncepi.call();
        for( int i=0; i<ncepi.nwired(); i++ ) {
          Node xxxret = ncepi.wired(i); // Neither newret nor oldret
          if( xxxret != newret && xxxret != oldret ) { // Not self-recursive
            if( xxxret instanceof RetNode ret ) {
              ret.fun().add_def(ncall);
              ret.fun().add_flow_uses();
            } else ((RootNode)xxxret).add_def(ncall);
          }
        }
        assert ncepi.is_CG(true);
      }
      // Find assert -> parm -> fun.
      // Move errors to the single unique caller arg.
      if( nn instanceof AssertNode a &&
          a.arg() instanceof ParmNode p && p.in(0)==fun )
        a._bad = path_call._badargs[p._idx-DSP_IDX];
    }
  }

  // Funs get special treatment by the H-M algo.
  @Override public boolean has_tvar() { return false; }

  // True if this is a forward_ref
  public ParmNode parm( int idx ) {
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx==idx )
        return (ParmNode)use;
    return null;
  }
  public ParmNode[] parms() {
    ParmNode[] parms = new ParmNode[nargs()];
    for( Node use : _uses )
      if( use instanceof ParmNode parm)
        parms[parm._idx] = parm;
    return parms;
  }
  public RetNode ret() {
    if( is_dead() ) return null;
    for( Node use : _uses )
      if( use instanceof RetNode ret ) {
        assert !ret.is_copy() && ret.len()==5;
        return ret;
      }
    return null;
  }
  // Returns FunPtr
  public FunPtrNode fptr() {
    RetNode ret = ret();
    if( ret==null ) return null;
    for( Node ruse : ret._uses )
      if( ruse instanceof FunPtrNode fptr )
        return fptr;
    return null;
  }

  @Override public boolean equals(Object o) { return this==o; } // Only one
  @Override public Node is_copy(int idx) {
    if( len()==1 ) return in(0); // Collapsing
    return in(0)==this ? in(1) : null;
  }
  void set_is_copy() { set_def(0,this); Env.GVN.add_reduce_uses(this); }

  @Override Node walk_dom_last( Predicate<Node> P) { return null; }

}
