package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;

import static com.cliffc.aa.AA.*;

// FunNodes are lexically scoped.  During parsing/graph-gen a closure is
// allocated for local variables as a standard NewObj.  Local escape analysis
// is used to remove NewObjs that do not escape the local lifetime.  Scoped
// variables pass in their NewObj pointer just "as if" a normal struct.
//
// Function bodies are self-contained; they only take data in through ParmNodes
// and ConNodes, and only control through the Fun.  They only return values
// through the Ret - including exposed lexically scoped uses.
//
// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// null, same as a C2 Region.  Args 1+ point to the callers control.  Before
// GCP/opto arg 1 points to ALL_CTRL as the generic unknown worse-case caller.
// ALL_CTRL is removed just prior to GCP, the precise call-graph is discovered,
// and calls are directly wired to the FunNode as part of GCP.  After GCP the
// call-graph is known precisely and is explicit in the graph.
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
// original Fun.  A FunPtr points to a Ret, and a Call will use a FunPtr (or a
// merge of FunPtrs) to indicate which function it calls.  After a call-graph
// edge is discovered, the Call is "wired" to the Fun.  A CallEpi points to the
// Ret, the Fun control points to a CProj to the Call, and each Parm points to
// a DProj (MProj) to the Call.  These direct edges allow direct data flow
// during gcp & iter.
//
// Memory both is and is-not treated special: the function body flows memory
// through from the initial Parm to the Ret in the normal way.  However the
// incoming memory argument is specifically trimmed by the Call to only those
// aliases used by the function body (either read or write), and the Ret only
// returns those memories explicitly written.  All the other aliases are
// treated as "pass-through" and explicitly routed around the Fun/Ret by the
// Call/CallEpi pair.


public class FunNode extends RegionNode {
  public String _name; // Optional for anon functions; can be set later via bind()
  public String _bal_close; // null for everything except "balanced functions", e.g. "[]"
  public int _fidx;
  public final TypeFunSig _sig;
  // Operator precedence; only set on top-level primitive wrappers.
  // -1 for normal non-operator functions and -2 for forward_decls.
  public final byte _op_prec;  // Operator precedence; only set on top-level primitive wrappers
  public final boolean _thunk_rhs;
  private byte _cnt_size_inlines; // Count of size-based inlines
  public static int _must_inline; // Used for asserts

  // Used to make the primitives at boot time.  Note the empty displays: in
  // theory Primitives should get the top-level primitives-display, but in
  // practice most primitives neither read nor write their own scope.
  public FunNode(           PrimNode prim) { this(prim._name,prim._sig,prim._op_prec,prim._thunk_rhs); }
  public FunNode(NewNode.NewPrimNode prim) { this(prim._name,prim._sig,prim._op_prec,false); }
  // Used to start an anonymous function in the Parser
  public FunNode(String[] flds, Type[] ts) { this(null,TypeFunSig.make(flds,TypeTuple.make_args(ts),TypeTuple.RET),-1,false); }
  // Used to forward-decl anon functions
  FunNode(String name) { this(name,TypeFunSig.make(TypeTuple.RET,TypeTuple.NO_ARGS),-2,false); add_def(Env.ALL_CTRL); }
  public FunNode(String name, TypeFunSig sig, int op_prec, boolean thunk_rhs ) { this(name,sig,op_prec,thunk_rhs,BitsFun.new_fidx()); }
  // Shared common constructor
  private FunNode(String name, TypeFunSig sig, int op_prec, boolean thunk_rhs, int fidx) {
    super(OP_FUN);
    _name = name;
    _fidx = fidx;
    _sig = sig;
    _op_prec = (byte)op_prec;
    _thunk_rhs = thunk_rhs;
    FUNS.setX(fidx(),this); // Track FunNode by fidx; assert single-bit fidxs
    keep();                 // Always keep, until RetNode is constructed
  }

  // Find FunNodes by fidx
  static Ary<FunNode> FUNS = new Ary<>(new FunNode[]{null,});
  public static void reset() { FUNS.clear(); _must_inline=0; }
  public static FunNode find_fidx( int fidx ) { return FUNS.atX(fidx); }
  int fidx() { return _fidx; }

  // Fast reset of parser state between calls to Exec

  // Short self name
  @Override public String xstr() { return name(); }
  // Inline longer info
  @Override public String str() { return is_forward_ref() ? xstr() : _sig.str(new SB(),new VBitSet(),null,false).toString(); }
  // Name from fidx alone
  private static String name( int fidx, boolean debug) {
    FunNode fun = find_fidx(fidx);
    return fun==null ? name(null,null,fidx,-1,false,debug) : fun.name(debug);
  }
  // Name from FunNode
  public String name(boolean debug) { return name(_name,_bal_close,fidx(),_op_prec,is_forward_ref(),debug); }
  String name() { return name(true); }
  static String name(String name, String bal, int fidx, int op_prec, boolean fref, boolean debug) {
    if( op_prec >= 0 && name != null ) name = '{'+name+(bal==null?"":bal)+'}'; // Primitives wrap
    if( name==null ) name="";
    if( debug ) name = name + "["+fidx+"]"; // FIDX in debug
    return fref ? "?"+name : name;          // Leading '?'
  }

  // Can return nothing, or "name" or "[name0,name1,name2...]" or "[35]"
  public static SB names(BitsFun fidxs, SB sb, boolean debug ) {
    int fidx = fidxs.abit();
    if( fidx >= 0 ) return sb.p(name(fidx,debug));
    if( fidxs==BitsFun.EMPTY ) return sb.p("[]");
    // See if this is just one common name, common for overloaded functions
    String s=null;
    boolean prim=false;
    for( Integer ii : fidxs ) {
      FunNode fun = find_fidx(ii);
      if( fun==null || fun._name==null ) { s=null; break; } // Unnamed fidx
      prim |= fun._op_prec >= 0;
      if( s==null ) s = fun._name;
      else if( !s.equals(fun._name) )
        { s=null; break; }
    }
    if( s!=null )
      if( prim ) sb.p('{').p(s).p('}'); else sb.p(s);
    // Make a list of the fidxs
    if( debug ) {
      int cnt = 0;
      sb.p('[');
      for( Integer ii : fidxs ) {
        if( ++cnt == 5 ) break;
        sb.p(ii).p(fidxs.above_center() ? '+' : ',');
      }
      if( cnt >= 5 ) sb.p("...");
      else sb.unchar();
      sb.p(']');
    }
    return sb;
  }

  // Debug only: make an attempt to bind name to a function
  public void bind( String tok ) {
    assert _name==null || _name.equals(tok); // Attempt to double-bind
    _name = tok;
  }

  // This function has disabled inlining
  public boolean noinline() { return _name != null && _name.startsWith("noinline") && in(0)==null; }

  // Never inline with a nested function
  @Override @NotNull public Node copy( boolean copy_edges) { throw unimpl(); }

  // True if may have future unknown callers.
  boolean has_unknown_callers() { return _defs._len > 1 && in(1) == Env.ALL_CTRL; }
  // Formal types.
  Type formal(int idx) {
    return idx == -1 ? TypeRPC.ALL_CALL : _sig.arg(idx);
  }
  public int nargs() { return _sig.nargs(); }
  void set_is_copy() { set_def(0,this); }

  // ----
  // Graph rewriting via general inlining.  All other graph optimizations are
  // already done.
  @Override public Node ideal_reduce() {
    Node rez = super.ideal_reduce();
    if( rez != null ) return rez;
    // Check for FunPtr/Ret dead/gone, and the function is no longer callable
    // from anybody.
    RetNode ret = ret();
    if( has_unknown_callers() && ret==null && _keep==0 ) {
      assert !is_prim();
      assert in(1)==Env.ALL_CTRL;
      return set_def(1,Env.XCTRL);
    }
    return null;
  }
  public Node ideal_inline(boolean check_progress) {
    // If no trailing RetNode and hence no FunPtr... function is uncallable
    // from the unknown caller.
    RetNode ret = ret();
    if( has_unknown_callers() && ret == null && Env.GVN._opt_mode != GVNGCM.Mode.Parse ) // Dead after construction?
      return null;

    if( is_forward_ref() ) return null; // No mods on a forward ref
    if( _defs._len <= 1  ) return null; // Not even the unknown caller
    ParmNode rpc_parm = rpc();
    if( rpc_parm == null ) return null; // Single caller const-folds the RPC, but also inlines in CallNode
    if( !check_callers() ) return null;
    if( _defs._len <= 2  ) return null; // No need to split callers if only 1

    // Every input path is wired to an output path
    for( int i=1+(has_unknown_callers() ? 1 : 0); i<_defs._len; i++ ) {
      Node c = in(i);
      if( !(c.in(0) instanceof CallNode) ) return null; // If this is not a CallNode, just bail
      CallNode call = (CallNode)c.in(0);
      CallEpiNode cepi = call.cepi();
      assert cepi._defs.find(ret)!= -1;  // If this is not wired, just bail
    }
    // Memory is not 'lifted' by DefMem, a sign that a bad-memory-arg is being
    // passed in.
    Node[] parms = parms();
    if( has_unknown_callers() ) {
      Node mem = parms[MEM_IDX];
      if( mem!=null && !mem._val.isa(Env.DEFMEM._val) )
        return null; // Do not inline a bad memory type
    }

    // Look for appropriate type-specialize callers
    TypeTuple formals = _thunk_rhs ? null : type_special(parms);
    Ary<Node> body = find_body(ret);
    int path = -1;              // Paths will split according to type
    if( formals == null ) {     // No type-specialization to do
      formals = _sig._formals;  // Use old args
      if( _cnt_size_inlines >= 10 && !is_prim() ) return null;
      // Large code-expansion allowed; can inline for other reasons
      path = _thunk_rhs ? 2 : split_size(body,parms); // Forcible size-splitting first path
      if( path == -1 ) return null;
      assert CallNode.ttfp(in(path).in(0).val()).fidx()!=-1; // called by a single-target call
      if( noinline() ) return null;
      if( !is_prim() ) _cnt_size_inlines++; // Disallow infinite size-inlining of recursive non-primitives
    }

    // Check for dups (already done this but failed to resolve all calls, so trying again).
    TypeTuple fformals = formals;
    if( path == -1 && FUNS.find(fun -> fun != null && !fun.is_dead() &&
                                fun._sig._formals==fformals && fun._sig._ret == _sig._ret &&
                                fun.in(1)==in(1) &&
                                Util.eq(_name,fun._name)) != -1 )
      return null;              // Done this before

    assert _must_inline==0; // Failed to inline a prior inline?
    if( path > 0 ) _must_inline = in(path).in(0)._uid;
    assert !check_progress;     // Not expecting progress

    // --------------
    // Split the callers according to the new 'fun'.
    GVNGCM.Mode old_mode = Env.GVN._opt_mode;
    Env.GVN._opt_mode = GVNGCM.Mode.Pause;
    FunNode fun = make_new_fun(ret, formals);
    split_callers(ret,fun,body,path);
    Env.GVN._opt_mode = old_mode;
    assert Env.START.more_flow(true)==0; // Initial conditions are correct
    return this;
  }
  @Override public Node ideal(GVNGCM gvn, int level) { throw com.cliffc.aa.AA.unimpl(); }

  @Override void unwire(int idx) {
    Node ctl = in(idx);
    if( !(ctl instanceof ConNode) ) {
      if( ctl.in(0)._op != OP_CALL ) return;
      CallNode call = (CallNode)ctl.in(0);
      CallEpiNode cepi = call.cepi();
      if( cepi != null ) {
        int ridx = cepi._defs.find(ret());
        if( ridx != -1 ) cepi.remove(ridx);
      }
    }
  }

  // Return false if any input path is dead (would rather fold away dead paths
  // before inlining), or if not exactly 1 return.
  private boolean check_callers( ) {
    // No dead input paths
    for( int i=1; i<_defs._len; i++ ) if( val(i)==Type.XCTRL && !in(i).is_prim() ) return false;
    // Gather the ParmNodes and the RetNode.  Ignore other (control) uses
    Node ret=null;
    for( Node use : _uses )
      if( use instanceof RetNode ) {
        if( ret!=null && ret!=use ) return false;
        ret = use;
      }
    return true;
  }

  // Visit all ParmNodes, looking for unresolved call uses that can be improved
  // by type-splitting
  private int find_type_split_index( Node[] parms ) {
    assert has_unknown_callers();// Only overly-wide calls.
    for( Node parm : parms )     // For all parms
      if( parm != null )         // (some can be dead)
        for( Node use : parm._uses ) { // See if a parm-user needs a type-specialization split
          if( use instanceof CallNode ) {
            CallNode call = (CallNode)use;
            if( (call.fdx()==parm && !parm.val().isa(TypeFunPtr.GENERIC_FUNPTR) ) ||
                call.fdx() instanceof UnresolvedNode ) { // Call overload not resolved
              Type t0 = parm.val(1);                   // Generic type in slot#1
              for( int i=2; i<parm._defs._len; i++ ) { // For all other inputs
                Type tp = parm.val(i);
                if( tp.above_center() ) continue; // This parm input is in-error
                Type ti = tp.widen();             // Get the widen'd type
                if( !ti.isa(t0) ) continue; // Must be isa-generic type, or else type-error
                if( ti != t0 ) return i; // Sharpens?  Then splitting here should help
              }
            }
            // Else no split will help this call, look for other calls to help
          }
        }

    return -1; // No unresolved calls; no point in type-specialization
  }

  // Find types for which splitting appears to help.
  private Type[] find_type_split( Node[] parms ) {
    assert has_unknown_callers(); // Only overly-wide calls.

    // Look for splitting to help an Unresolved Call.
    int idx = find_type_split_index(parms);
    if( idx != -1 ) {           // Found; split along a specific input path using widened types
      Type[] sig = Types.get(parms.length);
      sig[CTL_IDX] = Type.CTRL;
      sig[MEM_IDX] = TypeMem.MEM;
      sig[FUN_IDX] = parms[FUN_IDX]==null
        ? _sig.display().simple_ptr()
        : parms[FUN_IDX].val(idx);
      for( int i=ARG_IDX; i<parms.length; i++ )
        sig[i] = parms[i]==null ? Type.SCALAR : parms[i].val(idx).widen();
      return sig;
    }

    // Look for splitting to help a pointer from an unspecialized type
    boolean progress = false;
    Type[] sig = new Type[parms.length];
    Type tmem = parms[MEM_IDX].val();
    sig[CTL_IDX] = Type.CTRL;
    sig[MEM_IDX] = TypeMem.MEM;
    if( tmem instanceof TypeMem ) {
      for( int i=FUN_IDX; i<parms.length; i++ ) { // For all parms
        Node parm = parms[i];
        if( parm == null ) { sig[i]=Type.SCALAR; continue; } // (some can be dead)
        sig[i] = parm.val();                                 // Current type
        if( i==FUN_IDX ) continue;                           // No split on the display
        // Best possible type
        Type tp = Type.ALL;
        for( Node def : parm._defs )
          if( def != this )
            tp = tp.join(def.val());
        if( !(tp instanceof TypeMemPtr) ) continue; // Not a pointer
        TypeObj to = ((TypeMem)tmem).ld((TypeMemPtr)tp).widen(); //
        // Are all the uses of parm compatible with this TMP?
        // Also, flag all used fields.
        if( bad_mem_use(parm, to) )
          continue;               // So bad usage

        sig[i] = TypeMemPtr.make(BitsAlias.RECORD_BITS0,to); // Signature takes any alias but has sharper guts
        progress = true;
      }
    }
    if( progress ) return sig;

    return null;
  }

  // Check all uses are compatible with sharpening to a pointer.
  // TODO: Really should be a virtual call
  private static boolean bad_mem_use( Node n, TypeObj to) {
    for( Node use : n._uses ) {
      switch( use._op ) {
      case OP_NEWOBJ: break; // Field use is like store.value use
      case OP_IF: break;     // Zero check is ok
      case OP_CAST:          // Cast propagates check
        if( bad_mem_use(use, to) ) return true;
        break;
      case OP_LOAD:
        if( !(to instanceof TypeStruct) ||
            ((LoadNode)use).find((TypeStruct)to)== -1 )
          return true;          // Did not find field
        break;
      case OP_STORE:
        if( ((StoreNode)use).rez()==n) break; // Storing as value is ok
        if( !(to instanceof TypeStruct) ||    // Address needs to find field
            ((StoreNode)use).find((TypeStruct)to)== -1 )
          return true;          // Did not find field
        break;
      case OP_CALL: break; // Argument pass-thru probably needs to check formals
      case OP_RET: break;  // Return pass-thru should be ok
      case OP_NEWSTR:
        TypeFunSig sig = ((NewStrNode)use)._sig;
        Type formal = sig._formals.at(use._defs.find(n)-2);
        if( !TypeMemPtr.OOP0.dual().isa(formal) )
          return true;
        break;
      case OP_NAME: break; // Pointer to a nameable struct
      case OP_PRIM:
        if( use instanceof PrimNode.EQ_OOP ) break;
        if( use instanceof PrimNode.NE_OOP ) break;
        if( use instanceof MemPrimNode.LValueLength ) break;
        if( use instanceof MemPrimNode.LValueRead )
          if( ((MemPrimNode)use).idx() == n ) return true; // Use as index is broken
          else break;   // Use for array base is fine
        if( use instanceof MemPrimNode.LValueWrite || use instanceof MemPrimNode.LValueWriteFinal )
          if( ((MemPrimNode)use).idx() == n ) return true; // Use as index is broken
          else break;   // Use for array base or value is fine
        if( use instanceof PrimNode.MulF64 ) return true;
        if( use instanceof PrimNode.MulI64 ) return true;
        if( use instanceof PrimNode.AndI64 ) return true;
        if( use instanceof PrimNode.EQ_F64 ) return true;
        if( use instanceof PrimNode.EQ_I64 ) return true;
        throw unimpl();
      default: throw unimpl();
      }
    }
    return false;
  }


  // Look for type-specialization inlining.  If any ParmNode has an unresolved
  // Call user, then we'd like to make a clone of the function body (in least
  // up to getting all the Unresolved functions to clear out).  The specialized
  // code uses generalized versions of the arguments, where we only specialize
  // on arguments that help immediately.
  //
  // Same argument for field Loads from unspecialized values.
  private TypeTuple type_special( Node[] parms ) {
    if( !has_unknown_callers() ) return null; // Only overly-wide calls.
    Type[] sig = find_type_split(parms);
    if( sig == null ) return null; // No unresolved calls; no point in type-specialization
    // Make a new function header with new signature
    TypeTuple formals = TypeTuple.make_args(sig);
    if( !formals.isa(_sig._formals) ) return null;    // Fails in error cases
    return formals == _sig._formals ? null : formals; // Must see improvement
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
      if( op == OP_DEFMEM ) continue;       // Never part of body, but reachable from all allocations
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
    for( Node use : ret._uses ) // Include all FunPtrs as part of body
      if( use instanceof FunPtrNode )
        body.push(use);
    work.add(ret);
    while( !work.isEmpty() ) {  // While have work
      Node n = work.pop();      // Get work
      if( n==null ) continue;   // Defs can be null
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
    if( _defs._len <= 1 ) return -1; // No need to split callers if only 2
    boolean self_recursive=false;

    // Count function body size.  Requires walking the function body and
    // counting opcodes.  Some opcodes are ignored, because they manage
    // dependencies but make no code.
    int call_indirect=0, call_thunk=0; // Count of calls to e.g. loads/args/parms
    int[] cnts = new int[OP_MAX];
    for( Node n : body ) {
      int op = n._op;           // opcode
      if( op == OP_CALL ) {     // Call-of-primitive?
        Node n1 = ((CallNode)n).fdx();
        Node n2 = n1 instanceof UnresolvedNode ? n1.in(0) : n1;
        if( n2 instanceof FunPtrNode ) {
          FunPtrNode fpn = (FunPtrNode) n2;
          if( fpn.ret().rez() instanceof PrimNode )
            op = OP_PRIM;       // Treat as primitive for inlining purposes
          if( fpn.fun() == this ) self_recursive=true;
        } else if( n2.val()==TypeTuple.RET ) { // Thunks are encouraged to inline
          call_thunk++;
        } else
          call_indirect++;
      }
      cnts[op]++;               // Histogram ops
    }
    assert cnts[OP_FUN]==1 && cnts[OP_RET]==1;
    assert cnts[OP_SCOPE]==0;
    assert cnts[OP_REGION] <= cnts[OP_IF];

    // Specifically ignoring constants, parms, phis, rpcs, types,
    // unresolved, and casts.  These all track & control values, but actually
    // do not generate any code.
    if( cnts[OP_CALL] > 2 || // Careful inlining more calls; leads to exponential growth
        cnts[OP_LOAD] > 4 ||
        cnts[OP_STORE]> 2 ||
        cnts[OP_PRIM] > 6 ||   // Allow small-ish primitive counts to inline
        cnts[OP_NEWOBJ]>2 ||   // Display and return is OK
        (cnts[OP_NEWOBJ]>1 && self_recursive) ||
        call_indirect > 0 )
      return -1;

    // Pick which input to inline.  Only based on having some constant inputs
    // right now.
    Node mem = parms[MEM_IDX];  // Memory, used to sharpen input ptrs
    int m=-1, mncons = -1;
    for( int i=has_unknown_callers() ? 2 : 1; i<_defs._len; i++ ) {
      Node call = in(i).in(0);
      if( !(call instanceof CallNode) ) continue; // Not well formed
      if( ((CallNode)call).nargs() != nargs() ) continue; // Will not inline
      if( call.val() == Type.ALL ) continue; // Otherwise in-error
      if( ((CallNode)call).cepi()._keep>0 ) continue; // Call/CallEpi still being parsed
      TypeFunPtr tfp = CallNode.ttfp(call.val());
      int fidx = tfp.fidxs().abit();
      if( fidx < 0 || BitsFun.is_parent(fidx) ) continue;    // Call must only target one fcn
      if( self_recursive && body.find(call)!=-1 ) continue; // Self-recursive; amounts to unrolling
      int ncon=0;
      // Count constant inputs on non-error paths
      for( int j=MEM_IDX; j<parms.length; j++ ) {
        Node parm = parms[j];
        if( parm != null ) {    // Some can be dead
          Type actual = parm.in(i).sharptr(mem.in(i));
          Type formal = formal(j);
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

  private FunNode make_new_fun(RetNode ret, TypeTuple new_formals) {
    // Make a prototype new function header split from the original.
    int oldfidx = fidx();
    FunNode fun = new FunNode(_name,TypeFunSig.make(_sig._args,new_formals,_sig._ret),_op_prec,_thunk_rhs,BitsFun.new_fidx(oldfidx));
    fun._bal_close = _bal_close;
    fun.pop();                  // Remove null added by RegionNode, will be added later
    fun.unkeep();               // Ret will clone and not construct
    // Renumber the original as well; the original _fidx is now a *class* of 2
    // fidxs.  Each FunNode fidx is only ever a constant, so the original Fun
    // becomes the other child fidx.
    int newfidx = _fidx = BitsFun.new_fidx(oldfidx);
    FUNS.setX(newfidx,this);    // Track FunNode by fidx
    FUNS.clear(oldfidx);        // Old fidx no longer refers to a single FunNode
    ret.set_fidx(newfidx);      // Renumber in the old RetNode
    // Right now, force the type upgrade on old_fptr.  old_fptr carries the old
    // parent FIDX and is on the worklist.  Eventually, it comes off and the
    // value() call lifts to the child fidx.  Meanwhile its value can be used
    // to wire a size-split to itself (e.g. fib()), which defeats the purpose
    // of a size-split (single caller only, so inlines).
    for( Node old_fptr : ret._uses )
      if( old_fptr instanceof FunPtrNode ) // Can be many old funptrs with different displays
        old_fptr.xval();                   // Upgrade FIDX
    Env.GVN.add_flow(ret);
    Env.GVN.add_flow(this);
    Env.GVN.add_flow_uses(this);
    return fun;
  }

  // ---------------------------------------------------------------------------
  // Clone the function body, and split the callers of 'this' into 2 sets; one
  // for the old and one for the new body.  The new function may have a more
  // refined signature, and perhaps no unknown callers.
  //
  // When doing type-based splitting the old and new FunPtrs are gathered into
  // an Unresolved which replaces the old uses.  When doing path-based
  // splitting, the one caller on the split path is wired to the new function,
  // and all other calls keep their original FunPtr.
  //
  // Wired calls: unwire all calls *to* this function, including self-calls.
  // Clone the function; wire calls *from* the clone same as the original.
  // Then rewire all calls that were unwired; for a type-split wire both targets
  // with an Unresolved.  For a path-split rewire left-or-right by path.
  private void split_callers( RetNode oldret, FunNode fun, Ary<Node> body, int path ) {
    // Unwire this function and collect unwired calls.  Leave the
    // unknown-caller, if any.
    CallNode path_call = path < 0 ? null : (CallNode)in(path).in(0);
    Ary<CallEpiNode> unwireds = new Ary<>(new CallEpiNode[1],0);
    final int zlen = has_unknown_callers() ? 2 : 1;
    while( _defs._len > zlen ) {             // For all paths (except unknown-caller)
      CallNode call = (CallNode)pop().in(0); // Unhook without removal
      CallEpiNode cepi = call.cepi();
      cepi.del(cepi._defs.find(oldret));
      unwireds.add(cepi);
      Env.GVN.add_reduce(cepi); // Visit for inlining later
      // And remove path from all Parms
      for( Node parm : _uses )
        if( parm instanceof ParmNode )
          parm.pop();
    }

    // Map from old to cloned function body
    HashMap<Node,Node> map = new HashMap<>();
    // Collect aliases that are cloning.
    BitSet aliases = new BitSet();
    // Clone the function body
    map.put(this,fun);
    for( Node n : body ) {
      if( n==this ) continue;   // Already cloned the FunNode
      int old_alias = n instanceof NewNode ? ((NewNode)n)._alias : -1;
      Node c = n.copy(false);     // Make a blank copy with no edges
      map.put(n,c);               // Map from old to new
      if( old_alias != -1 )       // Was a NewNode?
        aliases.set(old_alias);   // Record old alias before copy/split
      // Slightly better error message when cloning constructors
      if( path > 0 ) {
        if( n instanceof IntrinsicNode ) ((IntrinsicNode)c)._badargs = path_call._badargs[1];
        if( n instanceof   MemPrimNode ) ((  MemPrimNode)c)._badargs = path_call._badargs;
      }
    }

    // Fill in edges.  New Nodes point to New instead of Old; everybody
    // shares old nodes not in the function (and not cloned).
    for( Node n : map.keySet() ) {
      Node c = map.get(n);
      assert c._defs._len==0;
      for( Node def : n._defs ) {
        Node newdef = map.get(def);// Map old to new
        c.add_def(newdef==null ? def : newdef);
      }
    }

    // Keep around the old body, even as the FunPtrs get shuffled from Call to Call
    for( Node use : oldret._uses ) if( use instanceof FunPtrNode ) use.keep();

    // Collect the old/new returns and funptrs and add to map also.  The old
    // Ret has a set (not 1!) of FunPtrs, one per unique Display.
    RetNode newret = (RetNode)map.get(oldret);
    newret._fidx = fun.fidx();
    if( path < 0 ) {            // Type split
      for( Node use : oldret._uses )
        if( use instanceof FunPtrNode ) {
          // Make an Unresolved choice of the old and new functions, to be used
          // by non-application uses.  E.g., passing a unresolved function
          // pointer to a 'map()' call, or storing it to memory.
          Node old_funptr = use;
          Node new_funptr = map.get(old_funptr);
          new_funptr.insert(old_funptr);
          new_funptr.xval(); // Build type so Unresolved can compute type
          UnresolvedNode new_unr = new UnresolvedNode(null,new_funptr);
          old_funptr.insert(new_unr);
          new_unr.add_def(old_funptr);
          new_unr._val = new_unr.value(GVNGCM.Mode.PesiNoCG);
        }
    } else {                           // Path split
      Node old_funptr = path_call.fdx(); // Find the funptr for the path split
      Node new_funptr = map.get(old_funptr);
      new_funptr.insert(old_funptr);
      TypeFunPtr ofptr = (TypeFunPtr) old_funptr.val();
      path_call.set_fdx(new_funptr); // Force new_funptr, will re-wire later
      TypeFunPtr nfptr = TypeFunPtr.make(BitsFun.make0(newret._fidx),ofptr._nargs,TypeMemPtr.NO_DISP);
      path_call._val = CallNode.set_ttfp((TypeTuple) path_call.val(),nfptr);
    } // Else other funptr/displays on unrelated path, dead, can be ignored

    // For all aliases split in this pass, update in-node both old and new.
    // This changes their hash, and afterwards the keys cannot be looked up.
    for( Map.Entry<Node,Node> e : map.entrySet() )
      if( e.getKey() instanceof MemSplitNode )
        ((MemSplitNode)e.getKey()).split_alias(e.getValue(),aliases);

    // Wired Call Handling:
    if( has_unknown_callers() ) { // Not called by any unknown caller
      if( path < 0 ) {            // Type Split
        // Change the unknown caller parm types to match the new sig.  Default
        // memory includes the other half of alias splits, which might be
        // passed in from recursive calls.
        for( Node p : fun._uses )
          if( p instanceof ParmNode ) {
            ParmNode parm = (ParmNode)p;
            parm.set_def(1,parm._idx==MEM_IDX ? Env.DEFMEM : Node.con(fun.formal(parm._idx).simple_ptr()));
          }
      } else                     // Path Split
        fun.set_def(1,Env.XCTRL);
    }

    // Put all new nodes into the GVN tables and worklist
    for( Map.Entry<Node,Node> e : map.entrySet() ) {
      Node oo = e.getKey();     // Old node
      Node nn = e.getValue();   // New node
      Type nt = oo.val();        // Generally just copy type from original nodes
      if( nn instanceof MrgProjNode ) { // Cloned allocations registers with default memory
        MrgProjNode nnrg = (MrgProjNode)nn;
        MrgProjNode oorg = (MrgProjNode)oo;
        Env.DEFMEM.make_mem(nnrg.nnn()._alias,nnrg);
        Env.DEFMEM.make_mem(oorg.nnn()._alias,oorg);
        int oldalias = BitsAlias.parent(oorg.nnn()._alias);
        Env.DEFMEM.set_def(oldalias,Node.con(TypeObj.UNUSED));
        oorg.reset_tvar();      // Force new H-M unification of memory
        Env.GVN.add_mono(oorg.nnn());
      }

      if( nn instanceof FunPtrNode ) { // FunPtrs pick up the new fidx
        TypeFunPtr ofptr = (TypeFunPtr)nt;
        if( ofptr.fidx()==oldret._fidx )
          nt = TypeFunPtr.make(BitsFun.make0(newret._fidx),ofptr._nargs,ofptr._disp);
      }
      nn._val = nt;             // Values
      nn._elock();              // In GVN table
    }
    Env.DEFMEM.xval();

    // Eagerly lift any Unresolved types, so they quit propagating the parent
    // (and both children) to all targets.
    for( Node fptr : oldret._uses )
      if( fptr instanceof FunPtrNode )
        for( Node unr : fptr._uses )
          if( unr instanceof UnresolvedNode )
            unr._val = unr.value(GVNGCM.Mode.PesiCG);

    // Rewire all unwired calls.
    for( CallEpiNode cepi : unwireds ) {
      CallNode call = cepi.call();
      CallEpiNode cepi2 = (CallEpiNode)map.get(cepi);
      if( path < 0 ) {          // Type-split, wire both & resolve later
        BitsFun call_fidxs = ((TypeFunPtr) call.fdx().val()).fidxs();
        assert call_fidxs.test_recur(    fidx());
        assert call_fidxs.test_recur(fun.fidx());
        cepi.wire1(call,this,oldret);
        cepi.wire1(call, fun,newret);
        if( cepi2!=null ) {
          // Found an unwired call in original: musta been a recursive
          // self-call.  wire the clone, same as the original was wired, so the
          // clone keeps knowledge about its return type.
          CallNode call2 = cepi2.call();
          BitsFun call_fidxs2 = ((TypeFunPtr) call2.fdx().val()).fidxs();
          assert call_fidxs2.test_recur(    fidx());
          assert call_fidxs2.test_recur(fun.fidx());
          cepi2.wire1(call2,this,oldret);
          cepi2.wire1(call2, fun,newret);
        }
      } else {                  // Non-type split, wire left or right
        if( call==path_call ) cepi.wire1(call, fun,newret);
        else                  cepi.wire1(call,this,oldret);
        if( cepi2!=null && cepi2.call()!=path_call ) {
          CallNode call2 = cepi2.call();
          // Found an unwired call in original: musta been a recursive
          // self-call.  wire the clone, same as the original was wired, so the
          // clone keeps knowledge about its return type.
          cepi2.wire1(call2,this,oldret);
          call2.xval();
          Env.GVN.add_flow_uses(this); // This gets wired, that gets wired, revisit all
        }
        Env.GVN.add_unuse(cepi);
      }
    }

    // Look for wired new not-recursive CallEpis; these will have an outgoing
    // edge to some other RetNode, but the Call will not be wired.  Wire.
    for( Node nn : map.values() ) {
      if( nn instanceof CallEpiNode ) {
        CallEpiNode ncepi = (CallEpiNode)nn;
        for( int i=0; i<ncepi.nwired(); i++ ) {
          RetNode xxxret = ncepi.wired(i); // Neither newret nor oldret
          if( xxxret != newret && xxxret != oldret ) { // Not self-recursive
            ncepi.wire0(ncepi.call(),xxxret.fun());
          }
        }
      }
    }

    // Retype memory, so we can everywhere lift the split-alias parents "up and
    // out".
    retype_mem(aliases,this.parm(MEM_IDX));
    retype_mem(aliases,fun .parm(MEM_IDX));

    // Unhook the hooked FunPtrs
    for( Node use : oldret._uses ) if( use instanceof FunPtrNode ) use.unkeep();
  }


  // Walk all memory edges, and 'retype' them, probably DOWN (counter to
  // 'iter').  Used when inlining, and the inlined body needs to acknowledge
  // bypasses aliases.  Used during code-clone, to lift the split alias parent
  // up & out.
  private static void retype_mem(BitSet aliases, Node mem) {
    Ary<Node> work = new Ary<>(new Node[1],0);
    work.push(mem);
    // Update all memory ops
    while( !work.isEmpty() ) {
      Node wrk = work.pop();
      if( wrk.is_mem() ) {
        Type twrk = wrk.val();
        Type tmem0 = twrk instanceof TypeTuple ? ((TypeTuple)twrk).at(1) : twrk;
        if( !(tmem0 instanceof TypeMem) ) continue;
        // Has any used values?
        if( has_used((TypeMem)tmem0,aliases) ) {
          Type tval = wrk.value(Env.GVN._opt_mode);
          if( twrk != tval ) {
            wrk._val= tval;
            Env.GVN.add_flow_uses(wrk);
            if( wrk instanceof MProjNode && wrk.in(0) instanceof CallNode ) {
              CallEpiNode cepi = ((CallNode)wrk.in(0)).cepi();
              if( cepi != null ) work.push(cepi);
            } else if( !(wrk instanceof RetNode) )
              work.addAll(wrk._uses);
          }
        }
      }
    }
  }

  private static boolean has_used(TypeMem tmem, BitSet aliases) {
    for( int alias = aliases.nextSetBit(0); alias != -1; alias = aliases.nextSetBit(alias + 1))
      if( tmem.at(alias)!= TypeObj.UNUSED )
        return true;            // Has a not-unused (some used) type
    return false;
  }

  // Compute value from inputs.  Simple meet over inputs.
  @Override public Type value(GVNGCM.Mode opt_mode) {
    // Will be an error eventually, but act like its executed so the trailing
    // EpilogNode gets visited during GCP
    if( is_forward_ref() ) return Type.CTRL;
    if( _defs._len==2 && in(1)==this ) return Type.XCTRL; // Dead self-loop
    if( in(0)==this ) return _defs._len>=2 ? val(1) : Type.XCTRL; // is_copy
    for( int i=1; i<_defs._len; i++ ) {
      Type c = val(i);
      if( c != Type.CTRL && c != Type.ALL ) continue; // Not control
      if( !(in(i) instanceof CProjNode) ) return Type.CTRL; // A constant control
      // Call might be alive and executing and calling many targets, just not this one.
      CallNode call = (CallNode)in(i).in(0);
      if( call._val == Type.ALL )
        return Type.CTRL;
      TypeFunPtr ttfp = CallNode.ttfpx(call._val);
      if( ttfp != null && !ttfp.above_center() && ttfp._fidxs.test_recur(_fidx) )
        return Type.CTRL;       // Call us
    }
    return Type.XCTRL;
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _op_prec==-2; }
  public ParmNode parm( int idx ) {
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx==idx )
        return (ParmNode)use;
    return null;
  }
  @Override public Node[] parms() {
    Node[] parms = new Node[nargs()];
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx != -1 )
        parms[((ParmNode)use)._idx] = use;
    assert parms[0]==null;
    parms[0] = this;
    return parms;
  }
  public ParmNode rpc() { return parm(-1); }
  public RetNode ret() {
    for( Node use : _uses )
      if( use instanceof RetNode && use._defs._len==5 && !((RetNode)use).is_copy() && ((RetNode)use).fun()==this )
        return (RetNode)use;
    return null;
  }

  @Override public boolean equals(Object o) { return this==o; } // Only one
  @Override public Node is_copy(int idx) { return null; }       // Never a copy, since inline rules are complex
}
