package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;

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
// Parm#0 and up (NOT the zero-slot but the zero idx) are the classic function
// arguments; Parm#-1 is for the RPC and Parm#-2 is for memory.
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
  public int _fidx;
  public final TypeFunSig _sig;
  // Operator precedence; only set on top-level primitive wrappers.
  // -1 for normal non-operator functions and -2 for forward_decls.
  private final byte _op_prec;  // Operator precedence; only set on top-level primitive wrappers
  private byte _cnt_size_inlines; // Count of size-based inlines

  // Used to make the primitives at boot time.  Note the empty displays: in
  // theory Primitives should get the top-level primitives-display, but in
  // practice most primitives neither read nor write their own scope.
  public FunNode(        PrimNode prim) { this(prim._name,prim._sig,prim.op_prec()); }
  public FunNode(IntrinsicNewNode prim) { this(prim._name,prim._sig,prim.op_prec()); }
  // Used to start an anonymous function in the Parser
  public FunNode(String[] flds, Type[] ts) { this(null,TypeFunSig.make(TypeStruct.make_args(flds,ts),Type.SCALAR),-1); }
  // Used to forward-decl anon functions
  FunNode(String name) { this(name,TypeFunSig.make(TypeStruct.NO_ARGS,Type.SCALAR),-2); add_def(Env.ALL_CTRL); }
  public FunNode(String name, TypeFunSig sig, int op_prec) { this(name,sig,op_prec,BitsFun.new_fidx()); }
  // Shared common constructor
  private FunNode(String name, TypeFunSig sig, int op_prec, int fidx) {
    super(OP_FUN);
    _name = name;
    _fidx = fidx;
    _sig = sig;
    _op_prec = (byte)op_prec;
    FUNS.setX(fidx(),this); // Track FunNode by fidx; assert single-bit fidxs
  }

  // Find FunNodes by fidx
  static Ary<FunNode> FUNS = new Ary<>(new FunNode[]{null,});
  public static void reset() { FUNS.clear(); }
  public static FunNode find_fidx( int fidx ) { return fidx >= FUNS._len ? null : FUNS.at(fidx); }
  int fidx() { return _fidx; }

  // Fast reset of parser state between calls to Exec

  // Short self name
  @Override String xstr() { return name(); }
  // Inline longer info
  @Override public String str() { return is_forward_ref() ? xstr() : _sig.str(null); }
  // Name from fidx alone
  private static String name( int fidx, boolean debug) {
    FunNode fun = find_fidx(fidx);
    return fun==null ? name(null,fidx,-1,false,debug) : fun.name(debug);
  }
  // Name from FunNode
  String name(boolean debug) { return name(_name,fidx(),_op_prec,is_forward_ref(),debug); }
  String name() { return name(true); }
  static String name(String name, int fidx, int op_prec, boolean fref, boolean debug) {
    if( op_prec >= 0 && name != null ) name = '{'+name+'}'; // Primitives wrap
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
  @Override @NotNull Node copy( boolean copy_edges, GVNGCM gvn) { throw AA.unimpl(); }

  // True if may have future unknown callers.
  boolean has_unknown_callers() { return _defs._len > 1 && in(1) == Env.ALL_CTRL; }
  // Formal types.
  Type formal(int idx) {
    return idx == -1 ? TypeRPC.ALL_CALL :
      (idx == -2 ? TypeMem.MEM : _sig.arg(idx));
  }
  int nargs() { return _sig.nargs(); } // Slot 0 is the return and not an arg, and is included in the length
  void set_is_copy(GVNGCM gvn) { gvn.set_def_reg(this,0,this); }

  // ----
  @Override public Node ideal(GVNGCM gvn, int level) {
    // Generic Region ideal
    Node n = super.ideal(gvn, level);
    if( n!=null ) return n;

    // If no trailing RetNode and hence no FunPtr... function is uncallable
    // from the unknown caller.
    RetNode ret = ret();
    if( has_unknown_callers() && ret == null && gvn._opt_mode != 0 ) { // Dead after construction?
      set_def(1,gvn.con(Type.XCTRL),gvn); // Kill unknown caller
      return this;
    }

    if( is_forward_ref() ) return null; // No mods on a forward ref
    if( _defs._len <= 1 ) return null; // Not even the unknown caller
    ParmNode rpc_parm = rpc();
    if( rpc_parm == null ) return null; // Single caller const-folds the RPC, but also inlines in CallNode
    ParmNode[] parms = new ParmNode[nargs()];
    if( split_callers_gather(gvn,parms) == null ) return null;

    if( _defs._len <= 2 ) return null; // No need to split callers if only 1

    if( level <= 1 ) {          // Only doing small-work now
      if( level==0 ) gvn.add_work2(this); // Maybe want to inline later, but not during asserts
      return null;
    }

    //----------------
    // level 2 (or 3) work: heuristics & inline

    // Every input path is wired to an output path
    if( _defs._len != ret._uses._len+(has_unknown_callers() ? 1 : 0) )
      return null;

    // Look for appropriate type-specialize callers
    TypeStruct formals = type_special(gvn, parms);
    Ary<Node> body = find_body(ret);
    int path = -1;              // Paths will split according to type
    if( formals == null ) {     // No type-specialization to do
      formals = _sig._formals;  // Use old args
      if( _cnt_size_inlines >= 10 && !is_prim() ) return null;
      // Large code-expansion allowed; can inline for other reasons
      path = split_size(gvn,body,parms);
      if( path == -1 ) return null;
      if( noinline() ) return null;
      if( !is_prim() ) _cnt_size_inlines++; // Disallow infinite size-inlining of recursive non-primitives
    }
    assert level==2; // Do not actually inline, if just checking that all forward progress was found

    // --------------
    // Split the callers according to the new 'fun'.
    int old_fidx = fidx();
    FunNode fun = make_new_fun(gvn, ret, formals);
    split_callers(gvn,ret,fun,body,path,old_fidx);
    assert Env.START.more_flow(gvn,new VBitSet(),true,0)==0; // Initial conditions are correct
    return this;
  }

  @Override void unwire(GVNGCM gvn,int idx) {
    Node ctl = in(idx);
    if( !(ctl instanceof ConNode) ) {
      CallNode call = (CallNode)ctl.in(0);
      CallEpiNode cepi = call.cepi();
      if( cepi != null ) {
        int ridx = cepi._defs.find(ret());
        gvn.remove_reg(cepi,ridx);
      }
    }
    // Single-target CallEpi can now inline
    RetNode ret = ret();
    if( _defs._len==3 && ret != null ) gvn.add_work_uses(ret);
  }

  // Gather the ParmNodes into an array.  Return null if any input path is dead
  // (would rather fold away dead paths before inlining).
  private RetNode split_callers_gather( GVNGCM gvn, ParmNode[] parms ) {
    for( int i=1; i<_defs._len; i++ ) if( gvn.type(in(i))==Type.XCTRL ) return null;

    // Gather the ParmNodes and the RetNode.  Ignore other (control) uses
    RetNode ret = null;
    for( Node use : _uses )
      if( use instanceof ParmNode ) {
        ParmNode parm = (ParmNode)use;
        if( parm._idx >= 0 ) // Skip memory, rpc
          parms[parm._idx] = parm;
      } else if( use instanceof RetNode ) { assert ret==null || ret==use; ret = (RetNode)use; }
    return ret;                 // return (or null if dead)
  }

  // Visit all ParmNodes, looking for unresolved call uses that can be improved
  // by type-splitting
  private int find_type_split_index( GVNGCM gvn, ParmNode[] parms ) {
    assert has_unknown_callers(); // Only overly-wide calls.
    for( ParmNode parm : parms ) // For all parms
      if( parm != null && parm._idx > 0 ) // (some can be dead) and skipping the display
        for( Node call : parm._uses ) { // See if a parm-user needs a type-specialization split
          if( call instanceof CallNode &&
              ((CallNode)call).fun() instanceof UnresolvedNode ) { // Call overload not resolved
            Type t0 = gvn.type(parm.in(1));            // Generic type in slot#1
            for( int i=2; i<parm._defs._len; i++ ) {   // For all other inputs
              Type tp = gvn.type(parm.in(i));
              if( tp.above_center() ) continue;        // This parm input is in-error
              Type ti = tp.widen();                    // Get the widen'd type
              if( !ti.isa(t0) ) continue; // Must be isa-generic type, or else type-error
              if( ti != t0 ) return i; // Sharpens?  Then splitting here should help
            }
            // Else no split will help this call, look for other calls to help
          }
          //if( call instanceof TypeNode ) {
          //  Type t0 = gvn.type(parm.in(1));            // Generic type in slot#1
          //  for( int i=2; i<parm._defs._len; i++ ) {   // For all other inputs
          //    Type tp = gvn.type(parm.in(i));
          //    if( tp.above_center() ) continue;        // This parm input is in-error
          //    System.out.println("Can we sharpen by inlining here?");
          //  }
          //}
        }

    return -1; // No unresolved calls; no point in type-specialization
  }

  private Type[] find_type_split( GVNGCM gvn, ParmNode[] parms ) {
    assert has_unknown_callers(); // Only overly-wide calls.
    // Look for splitting to help an Unresolved Call.
    int idx = find_type_split_index(gvn,parms);
    if( idx != -1 ) {           // Found; split along a specific input path using widened types
      Type[] sig = TypeAry.get(parms.length);
      sig[0] = parms[0]==null
        ? _sig.display().make_from(TypeStr.NO_DISP)
        : gvn.type(parms[0].in(idx));
      for( int i=1; i<parms.length; i++ ) // 0 for display
        sig[i] = parms[i]==null ? Type.SCALAR : gvn.type(parms[i].in(idx)).widen();
      return sig;
    }

    // Look for splitting to help a field Load from an unspecialized type.
    // Split ~Scalar,~nScalar,~Oop,~nOop, ~Struct,~nStruct into ~Struct and add
    // fields discovered.
    boolean progress=false;
    Type[] sig = new Type[parms.length];
    for( int i=0; i<parms.length; i++ ) { // For all parms
      Node parm = parms[i];
      if( parm == null ) { sig[i]=Type.SCALAR; continue; } // (some can be dead)
      Type tp = gvn.type(parm);
      for( Node puse : parm._uses ) { // See if a parm-user needs a load specialization
        Type rez = find_load_use(puse,tp);
        if( rez != tp ) { progress = true; tp = rez; }
      }
      sig[i] = tp;
    }
    if( !progress ) return null;
    throw AA.unimpl();
  }

  private static Type find_load_use(Node puse, Type tp) {
    if( !tp.isa(TypeStruct.ANYSTRUCT) ) return tp;
    if( puse instanceof CastNode )
      throw AA.unimpl();
    if( puse instanceof LoadNode )
      throw AA.unimpl();
    return tp;                  // Unknown use, can ignore
  }


  // Look for type-specialization inlining.  If any ParmNode has an unresolved
  // Call user, then we'd like to make a clone of the function body (in least
  // up to getting all the Unresolved functions to clear out).  The specialized
  // code uses generalized versions of the arguments, where we only specialize
  // on arguments that help immediately.
  //
  // Same argument for field Loads from unspecialized values.
  private TypeStruct type_special( GVNGCM gvn, ParmNode[] parms ) {
    if( !has_unknown_callers() ) return null; // Only overly-wide calls.
    Type[] sig = find_type_split(gvn,parms);
    if( sig == null ) return null; // No unresolved calls; no point in type-specialization
    // Make a new function header with new signature
    TypeStruct formals = TypeStruct.make_args(_sig._formals._flds,sig);
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
    Ary<Node> body = new Ary<>(new Node[1],0);
    work.add(this);             // Prime worklist
    while( !work.isEmpty() ) {  // While have work
      Node n = work.pop();      // Get work
      if( freached.tset(n._uid) ) continue; // Already visited?
      int op = n._op;           // opcode
      if( op == OP_FUN  && n       != this ) continue; // Call to other function, not part of inlining
      if( op == OP_PARM && n.in(0) != this ) continue; // Arg  to other function, not part of inlining
      if( op == OP_DEFMEM ) continue;                  // Never part of body, but reachable from all allocations
      body.push(n);                                    // Part of body
      if( op == OP_RET ) continue;                     // Return (of this or other function)
      if( n instanceof ProjNode && n.in(0) instanceof CallNode ) continue; // Wired call; all projs lead to other functions
      work.addAll(n._uses);   // Visit all uses
    }

    //// Backwards walk, trimmed to reachable from forwards
    //VBitSet breached = new VBitSet(); // Backwards and forwards reached
    //work.add(ret);
    //while( !work.isEmpty() ) {  // While have work
    //  Node n = work.pop();      // Get work
    //  if( n==null ) continue;   // Defs can be null
    //  if( !freached.get (n._uid) ) continue; // Not reached from fcn top
    //  if(  breached.tset(n._uid) ) continue; // Already visited?
    //  body.push(n);                          // Part of body
    //  work.addAll(n._defs);                  // Visit all defs
    //  if( n.is_multi_head() )                // Multi-head?
    //    work.addAll(n._uses);                // All uses are ALSO part, even if not reachable in this fcn
    //}
    return body;
  }

  // Split a single-use copy (e.g. fully inline) if the function is "small
  // enough".  Include anything with just a handful of primitives, or a single
  // call, possible with a single if.
  private int split_size( GVNGCM gvn, Ary<Node> body, ParmNode[] parms ) {
    if( _defs._len <= 1 ) return -1; // No need to split callers if only 2
    BitSet recursive = new BitSet();    // Heuristic to limit unrolling recursive methods

    // Count function body size.  Requires walking the function body and
    // counting opcodes.  Some opcodes are ignored, because they manage
    // dependencies but make no code.
    int[] cnts = new int[OP_MAX];
    for( Node n : body ) {
      int op = n._op;           // opcode
      if( op == OP_CALL ) {     // Call-of-primitive?
        Node n1 = ((CallNode)n).fun();
        Node n2 = n1 instanceof UnresolvedNode ? n1.in(0) : n1;
        if( n2 instanceof FunPtrNode ) {
          FunPtrNode fpn = (FunPtrNode)n2;
          if( fpn.ret().val() instanceof PrimNode )
            op = OP_PRIM;       // Treat as primitive for inlining purposes
          if( fpn.fun() == this )
            recursive.set(n.in(0)._uid);  // No self-recursive inlining till after parse
        }
      }
      cnts[op]++;               // Histogram ops
    }
    assert cnts[OP_FUN]==1 && cnts[OP_RET]==1;
    assert cnts[OP_SCOPE]==0 && cnts[OP_TMP]==0;
    assert cnts[OP_REGION] <= cnts[OP_IF];

    // Pick which input to inline.  Only based on having some constant inputs
    // right now.
    Node mem = parm(-2);        // Memory, used to sharpen input ptrs
    int m=-1, mncons = -1;
    for( int i=has_unknown_callers() ? 2 : 1; i<_defs._len; i++ ) {
      Node call = in(i).in(0);
      if( !(call instanceof CallNode) ) continue; // Not well formed
      if( ((CallNode)call).nargs() != nargs() ) continue; // Will not inline
      TypeFunPtr tfp = CallNode.ttfp(gvn.type(call));
      int fidx = tfp.fidxs().abit();
      if( fidx < 0 ) continue;  // Call must only target one fcn
      int ncon=0;
      for( ParmNode parm : parms )
        if( parm != null ) {    // Some can be dead
          Type actual = gvn.sharptr(parm.in(i),mem.in(i));
          Type formal = formal(parm._idx);
          if( !actual.isa(formal) ) // Path is in-error?
            { ncon = -2; break; }   // This path is in-error, cannot inline even if small & constants
          if( actual.is_con() ) ncon++; // Count constants along each path
        }
      if( ncon > mncons && !recursive.get(in(i)._uid) )
        { mncons = ncon; m = i; } // Path with the most constants
    }
    if( m == -1 )               // No paths are not in-error? (All paths have an error-parm)
      return -1;                // No inline

    // Specifically ignoring constants, parms, phis, rpcs, types,
    // unresolved, and casts.  These all track & control values, but actually
    // do not generate any code.
    if( cnts[OP_CALL] > 2 || // Careful inlining more calls; leads to exponential growth
        cnts[OP_IF  ] > 1+mncons || // Allow some trivial filtering to inline
        cnts[OP_PRIM] > 6 )  // Allow small-ish primitive counts to inline
      return -1;

    return m;                   // Return path to split on
  }

  private FunNode make_new_fun(GVNGCM gvn, RetNode ret, TypeStruct new_formals) {
    // Make a prototype new function header split from the original.
    int oldfidx = fidx();
    FunNode fun = new FunNode(_name,TypeFunSig.make(new_formals,_sig._ret),_op_prec,BitsFun.new_fidx(oldfidx));
    fun.pop();                  // Remove null added by RegionNode, will be added later
    // Renumber the original as well; the original _fidx is now a *class* of 2
    // fidxs.  Each FunNode fidx is only ever a constant, so the original Fun
    // becomes the other child fidx.
    int newfidx = _fidx = BitsFun.new_fidx(oldfidx);
    FUNS.setX(newfidx,this);    // Track FunNode by fidx
    Type toldret = gvn.unreg(ret);// Remove before renumbering
    ret._fidx = newfidx;        // Renumber in the old RetNode
    gvn.rereg(ret,toldret);
    // Right now, force the type upgrade on old_fptr.  old_fptr carries the old
    // parent FIDX and is on the worklist.  Eventually, it comes off and the
    // value() call lifts to the child fidx.  Meanwhile its value can be used
    // to wire a size-split to itself (e.g. fib()), which defeats the purpose
    // of a size-split (single caller only, so inlines).
    FunPtrNode old_fptr = ret.funptr();
    gvn.setype(old_fptr,old_fptr.value(gvn));
    gvn.add_work_uses(old_fptr);
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
  private void split_callers( GVNGCM gvn, RetNode oldret, FunNode fun, Ary<Node> body, int path, int old_fidx ) {
    gvn.add_work(this);
    // Unwire this function and collect unwired calls.  Leave the
    // unknown-caller, if any.
    CallNode path_call = path < 0 ? null : (CallNode)in(path).in(0);
    Ary<CallEpiNode> unwireds = new Ary<>(new CallEpiNode[1],0);
    final int zlen = has_unknown_callers() ? 2 : 1;
    while( _defs._len > zlen ) {             // For all paths (except unknown-caller)
      CallNode call = (CallNode)pop().in(0); // Unhook without removal
      CallEpiNode cepi = call.cepi();
      { Type t = gvn.unreg(cepi);  cepi.del(cepi._defs.find(oldret));  gvn.rereg(cepi,t); }
      unwireds.add(cepi);
      // And remove path from all Parms
      for( Node parm : _uses )
        if( parm instanceof ParmNode )
          { Type t = gvn.unreg(parm); parm.pop(); gvn.rereg(parm,t); }
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
      Node c = n.copy(false,gvn); // Make a blank copy with no edges
      map.put(n,c);               // Map from old to new
      if( old_alias != -1 )       // Was a NewNode?
        aliases.set(old_alias);   // Record old alias before copy/split
      // Slightly better error message when cloning constructors
      if( path > 0 && n instanceof IntrinsicNode )
        ((IntrinsicNode)c)._badargs = path_call._badargs[1];
    }

    // Collect the old/new returns and funptrs and add to map also.
    RetNode newret = (RetNode)map.get(oldret);
    newret._fidx = fun.fidx();
    FunPtrNode old_funptr = oldret.funptr();
    FunPtrNode new_funptr = (FunPtrNode)old_funptr.copy(false,gvn);
    new_funptr.add_def(newret);
    new_funptr.add_def(old_funptr.in(1)); // Share same display
    TypeFunPtr ofptr = (TypeFunPtr)gvn.type(old_funptr);
    TypeFunPtr nfptr = TypeFunPtr.make(BitsFun.make0(newret._fidx),ofptr._nargs,ofptr._disp);
    gvn.rereg(new_funptr,nfptr);
    old_funptr.keep();

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

    // For all aliases split in this pass, update in-node both old and new.
    // This changes their hash, and afterwards the keys cannot be looked up.
    for( Map.Entry<Node,Node> e : map.entrySet() )
      if( e.getKey() instanceof MemMergeNode )
        ((MemMergeNode)e.getKey()).update_alias(e.getValue(),aliases,gvn);

    // Wired Call Handling:
    if( path < 0 ) {            // Type Split
      // Make an Unresolved choice of the old and new functions, to be used by
      // non-application uses.  E.g., passing a unresolved function pointer to
      // a 'map()' call, or storing it to memory.
      UnresolvedNode new_unr = new UnresolvedNode(null,new_funptr);
      gvn.replace(old_funptr,new_unr);
      new_unr.add_def(old_funptr);
      gvn.rereg(new_unr,new_unr.value(gvn));

      if( has_unknown_callers() ) {
        // Change the unknown caller parm types to match the new sig.  Default
        // memory includes the other half of alias splits, which might be
        // passed in from recursive calls.
        ParmNode parm;
        for( Node p : fun._uses )
          if( p instanceof ParmNode && (parm=(ParmNode)p)._idx != 0 )
            parm.set_def(1,parm._idx==-2 ? Env.DEFMEM : gvn.con(fun.formal(parm._idx)),gvn);
      }

    } else {                    // Path Split
      if( has_unknown_callers() ) // Not called by any unknown caller
        fun.set_def(1,gvn.con(Type.XCTRL),gvn);
    }

    // Put all new nodes into the GVN tables and worklist
    for( Map.Entry<Node,Node> e : map.entrySet() ) {
      Node oo = e.getKey();           // Old node
      Node nn = e.getValue();         // New node
      Type nt = gvn.type(oo);   // Generally just copy type from original nodes
      if( nn instanceof ParmNode && nn.in(0) == fun ) {  // Leading edge ParmNodes
        ParmNode pnn = (ParmNode)nn; // Update non-display type to match new signature
        if( pnn._idx > 0 ) nt = fun.formal(pnn._idx).simple_ptr(); // Upgrade new Parm default type
      }
      if( nn instanceof OProjNode ) { // Cloned allocations registers with default memory
        Env.DEFMEM.make_mem(gvn,(NewNode)nn.in(0),(OProjNode)nn);
        Env.DEFMEM.make_mem(gvn,(NewNode)oo.in(0),(OProjNode)oo);
        int oldalias = BitsAlias.parent(((NewNode)oo.in(0))._alias);
        gvn.set_def_reg(Env.DEFMEM,oldalias,gvn.con(TypeObj.UNUSED));
      }
      gvn.rereg(nn,nt);
    }

    if( path >= 0 ) {            // Path split
      path_call.set_fun_reg(new_funptr, gvn); // Force new_funptr, will re-wire later
      TypeTuple tt = (TypeTuple)gvn.type(path_call);
      gvn.setype(path_call, CallNode.set_ttfp(tt,nfptr));
    }

    // Rewire all unwired calls.
    for( CallEpiNode cepi : unwireds ) {
      CallNode call = cepi.call();
      CallEpiNode cepi2 = (CallEpiNode)map.get(cepi);
      if( path < 0 ) {          // Type-split, wire both & resolve later
        BitsFun call_fidxs = ((TypeFunPtr)gvn.type(call.fun())).fidxs();
        assert call_fidxs.test_recur(    fidx());
        assert call_fidxs.test_recur(fun.fidx());
        cepi.wire1(gvn,call,this,oldret);
        cepi.wire1(gvn,call, fun,newret);
        if( cepi2!=null ) {
          // Found an unwired call in original: musta been a recursive
          // self-call.  wire the clone, same as the original was wired, so the
          // clone keeps knowledge about its return type.
          CallNode call2 = cepi2.call();
          BitsFun call_fidxs2 = ((TypeFunPtr)gvn.type(call2.fun())).fidxs();
          assert call_fidxs2.test_recur(    fidx());
          assert call_fidxs2.test_recur(fun.fidx());
          cepi2.wire1(gvn,call2,this,oldret);
          cepi2.wire1(gvn,call2, fun,newret);
        }
      } else {                  // Non-type split, wire left or right
        if( call==path_call ) cepi.wire1(gvn,call, fun,newret);
        else                  cepi.wire1(gvn,call,this,oldret);
        if( cepi2!=null && cepi2.call()!=path_call ) {
          // Found an unwired call in original: musta been a recursive
          // self-call.  wire the clone, same as the original was wired, so the
          // clone keeps knowledge about its return type.
          cepi2.wire1(gvn,cepi2.call(),this,oldret);
        }
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
            ncepi.wire0(gvn,ncepi.call(),xxxret.fun(),xxxret);
          }
        }
      }
    }
    old_funptr.unkeep(gvn);
  }

  // Compute value from inputs.  Simple meet over inputs.
  @Override public Type value(GVNGCM gvn) {
    // Will be an error eventually, but act like its executed so the trailing
    // EpilogNode gets visited during GCP
    if( is_forward_ref() ) return Type.CTRL;
    
    // TODO: CNC BUG - Wired call paths from optional resolving calls are treated as 'true' Ctrl
    // even if dead.
    // Theory#1: do not wire unresolved
    // Theory#2: during GCP, check-back to CProj to Call & verify fidx is available.


    return super.value(gvn);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _op_prec==-2; }
  public ParmNode parm( int idx ) {
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx==idx )
        return (ParmNode)use;
    return null;
  }
  boolean is_parm( Node n ) { return n instanceof ParmNode && n.in(0)==this; }
  public ParmNode rpc() { return parm(-1); }
  public RetNode ret() {
    for( Node use : _uses )
      if( use instanceof RetNode && !((RetNode)use).is_copy() && ((RetNode)use).fun()==this )
        return (RetNode)use;
    return null;
  }

  @Override public boolean equals(Object o) { return this==o; } // Only one
  @Override public byte op_prec() { return _op_prec; }

}
