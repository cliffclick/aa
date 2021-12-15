package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
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


public class FunNode extends RegionNode {
  public String _name;      // Debug-only name
  public String _bal_close; // null for everything except "balanced oper functions", e.g. "[]"
  public int _fidx;         // Unique number for this piece of code
  public int _nargs;        // Number of arguments
  // Operator precedence; only set on top-level primitive wrappers.
  // -1 for normal non-operator functions and -2 for forward_decls.
  public byte _op_prec;  // Operator precedence; only set on top-level primitive wrappers
  // Function is generated from whole-cloth via classForName.clazz__node.  Gets
  // to keep-alive and have default types until inlined once, then gets
  // removed.
  public boolean _java_fun;

  // H-M non-generative set, only active during Combo.
  public TV2[] _nongen;

  private byte _cnt_size_inlines; // Count of size-based inlines; prevents infinite unrolling via inlining
  public static int _must_inline; // Used for asserts

  // Used to make the primitives at boot time.  Note the empty displays: in
  // theory Primitives should get the top-level primitives-display, but in
  // practice most primitives neither read nor write their own scope.
  public FunNode(String name,           PrimNode prim) { this(name, prim._tfp.fidx(),prim._op_prec,prim._tfp.nargs()); }
  public FunNode(String name,NewNode.NewPrimNode prim) { this(name, prim._tfp.fidx(),prim._op_prec,prim._tfp.nargs()); }
  // Used to start an anonymous function in the Parser
  public FunNode(int nargs) { this(null,-1, nargs); }
  // Used to forward-decl anon functions
  FunNode(String name) { this(name,-2, 0); add_def(Env.SCP_0); }
  // Shared common constructor for Named type constructors
  FunNode(String name, int op_prec, int nargs ) { this(name, BitsFun.new_fidx(),op_prec, nargs); }
  // Shared common constructor
  private FunNode( String name, int fidx, int op_prec, int nargs ) {
    super(OP_FUN);
    _name = name;
    _fidx = fidx;
    _nargs = nargs;
    _op_prec = (byte)op_prec;
    FUNS.setX(fidx(),this); // Track FunNode by fidx; assert single-bit fidxs
  }

  // Find FunNodes by fidx
  private static int FLEN;
  public static Ary<FunNode> FUNS = new Ary<>(new FunNode[]{null,});
  public static void init0() { FLEN = FUNS.len(); }
  public static void reset_to_init0() { FUNS.set_len(FLEN); _must_inline=0; }
  public static FunNode find_fidx( int fidx ) { return FUNS.atX(fidx); }
  int fidx() { return _fidx; }

  // Short self name
  @Override public String xstr() { return name(); }
  // Inline longer info
  @Override public String str() { return name(); }
  // Name from fidx alone
  private static String name( int fidx, boolean debug) {
    FunNode fun = find_fidx(fidx);
    return fun==null ? name(null,null,fidx,-1,debug) : fun.name(debug);
  }
  // Name from FunNode
  String name() { return name(true); }
  public String name(boolean debug) {
    String name = _name;
    if( name==null ) {
      FunPtrNode fptr = fptr();
      name=fptr==null ? null : fptr._name;
    }
    return name(name,_bal_close,fidx(),_op_prec,debug);
  }
  static String name(String name, String bal, int fidx, int op_prec, boolean debug) {
    if( op_prec >= 0 && name != null && bal!=null ) name = name+bal; // Primitives wrap
    if( name==null ) name="";
    if( debug ) name = name + "["+fidx+"]"; // FIDX in debug
    return name;
  }

  // Can return nothing, or "name" or "[name0,name1,name2...]" or "[35]"
  public static SB names(BitsFun fidxs, SB sb, boolean debug ) {
    int fidx = fidxs.abit();
    if( fidx >= 0 ) return sb.p(name(fidx,debug));
    if( fidxs==BitsFun.EMPTY ) return sb.p("[]");
    // See if this is just one common name, common for overloaded functions
    String s=null;
    for( Integer ii : fidxs ) {
      FunNode fun = find_fidx(ii);
      if( fun!=null ) {
        if( fun._name != null ) s = fun._name;
        else if( !fun.is_dead() )
          for( Node fptr : fun.ret()._uses ) // For all displays for this fun
            if( fptr instanceof FunPtrNode ) {
              String name = ((FunPtrNode)fptr)._name; // Get debug name
              if( s==null ) s=name;                   // Capture debug name
              else if( !Util.eq(s,name) )             // Same name is OK
                { s=null; break; } // Too many different names
            }
        if( s==null ) break; // Unnamed fidx
      }
    }
    if( s!=null )
      sb.p(s);
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
    if( _name==null ) _name = tok;
    if( !_name.equals(tok) ) // Attempt to double-bind
      _name = _name+":"+tok;
  }

  // This function has disabled inlining
  public boolean noinline() { return in(0)==null && name(false).startsWith("noinline"); }

  // Never inline with a nested function
  @Override @NotNull public Node copy( boolean copy_edges) { throw unimpl(); }

  // True if may have future unknown callers.
  public boolean has_unknown_callers() {
    return _defs._len >= 2 && in(1)==Env.ALL_CTRL;
  }
  // True if this function escapes the top-level scope
  boolean is_unknown_alive() {
    return _defs._len==1 || (in(1) instanceof ScopeNode && ((ScopeNode)in(1)).top_escapes().test_recur(_fidx));
  }

  public int nargs() { return _nargs; }

  // ----
  // Graph rewriting via general inlining.  All other graph optimizations are
  // already done.
  @Override public Node ideal_reduce() {
    // Common Region reductions; killing off dead paths
    Node rez = super.ideal_reduce();
    if( rez != null ) return rez;
    if( is_keep() ) return null; // FunNode still under construction
    // Check for FunPtr/Ret dead/gone, and the function is no longer callable
    // from anybody.
    if( has_unknown_callers() && ret()==null ) {
      assert !is_prim();
      if( _defs._len<= 1 ) return null;
      for( Node use : _uses ) { // All parms can lift
        Env.GVN.add_flow(use);
        Env.GVN.add_flow_defs(use); //
      }
      return set_def(1,Env.XCTRL);
    }
    // Backdoor hook to trigger FunPtr dropping a unused display
    FunPtrNode fptr = fptr();
    if( parm(DSP_IDX)==null && fptr !=null && !(fptr.display() instanceof ConNode) )
      Env.GVN.add_reduce(fptr);

    return null;
  }

  public Node ideal_inline(boolean check_progress) {
    // If no trailing RetNode and hence no FunPtr... function is uncallable
    // from the unknown caller.
    RetNode ret = ret();
    if( has_unknown_callers() && ret == null ) // Dead after construction?
      return null;

    Node[] parms = parms();
    Node rpc_parm = parms[0];
    if( rpc_parm == null ) return null; // Single caller const-folds the RPC, but also inlines in CallNode
    if( !check_callers() ) return null;
    if( _defs._len <= 2  ) return null; // No need to split callers if only 1

    // Every input path is wired to an output path
    for( int i=1+(has_unknown_callers() ? 1 : 0); i<_defs._len; i++ ) {
      Node c = in(i);
      if( !(c.in(0) instanceof CallNode) ) return null; // If this is not a CallNode, just bail
      CallNode call = (CallNode)c.in(0);
      CallEpiNode cepi = call.cepi();
      if( cepi==null ) return null;
      assert cepi._defs.find(ret)!= -1;  // If this is not wired, just bail
    }

    // Look for appropriate type-specialize callers
    TypeStruct formals = type_special(parms);
    Ary<Node> body = find_body(ret);
    int path = -1;              // Paths will split according to type
    if( formals == null ) {     // No type-specialization to do
      if( _cnt_size_inlines >= 10 && !is_prim() ) return null;
      // Large code-expansion allowed; can inline for other reasons
      path = split_size(body,parms); // Forcible size-splitting first path
      if( path == -1 ) return null;
      assert CallNode.ttfp(in(path).val(0)).fidx()!=-1; // called by a single-target call
      Node fdx = ((CallNode)in(path).in(0)).fdx();
      assert fdx instanceof FunPtrNode; // Shoulda cleared out
      body.add(fdx);
      if( !is_prim() ) _cnt_size_inlines++; // Disallow infinite size-inlining of recursive non-primitives
    }

    if( noinline() ) return null;

    assert _must_inline==0; // Failed to inline a prior inline?
    if( path > 0 ) _must_inline = in(path).in(0)._uid;
    assert !check_progress;     // Not expecting progress

    // --------------
    // Split the callers according to the new 'fun'.
    FunNode fun = make_new_fun(ret, path);
    split_callers(ret,fun,body,path);
    assert Env.START.more_work(true)==0; // Initial conditions are correct
    return this;
  }

  @Override void unwire(int idx) {
    Node ctl = in(idx);
    if( !(ctl instanceof ConNode) ) {
      if( ctl.in(0)._op != OP_CALL ) return;
      CallNode call = (CallNode)ctl.in(0);
      CallEpiNode cepi = call.cepi();
      if( cepi != null ) {
        int ridx = cepi._defs.find(ret());
        if( ridx != -1 ) Env.GVN.add_flow(cepi).remove(ridx);
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
            Node fdx = call.fdx();
            if( fdx instanceof FreshNode ) fdx = ((FreshNode)fdx).id();
            if( (fdx==parm && !parm._val.isa(TypeFunPtr.GENERIC_FUNPTR) ) ||
                fdx instanceof UnresolvedNode ) { // Call overload not resolved
              Type t0 = parm.val(1);                   // Generic type in slot#1
              for( int i=2; i<parm._defs._len; i++ ) { // For all other wired inputs
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
  private TypeStruct find_type_split( Node[] parms ) {
    assert has_unknown_callers(); // Only overly-wide calls.

    // Look for splitting to help an Unresolved Call.
    int idx = find_type_split_index(parms);
    if( idx != -1 ) {           // Found; split along a specific input path using widened types
      //TypeStruct formals = _sig._formals;
      //for( TypeFld fld : formals.flds() ) {
      //  Node parm = parms[fld._order];
      //  TypeFld fld2 = fld.make_from(parm==null ? Type.ALL : parm.val(idx).widen());
      //  if( fld2.isa(fld) )
      //    formals = formals.replace_fld(fld2);
      //}
      //return formals;
      throw unimpl();
    }

    // Look for splitting to help a pointer from an unspecialized type
    Type tmem = parms[MEM_IDX]._val;
    if( tmem instanceof TypeMem ) {
      boolean progress = false;
      TypeStruct formals = TypeStruct.ALLSTRUCT;
      for( int i=DSP_IDX; i<parms.length; i++ ) { // For all parms
        if( i==DSP_IDX ) continue; // No split on the display
        ParmNode parm = (ParmNode)parms[i];
        if( parm == null ) continue;            // (some can be dead)
        if( parm._val==Type.ALL ) return null;  // No split with error args
        // Best possible type
        Type tp = Type.ALL;
        for( Node def : parm._defs )
          if( def != this )
            tp = tp.join(def._val);
        formals = formals.add_fld(parm._name, TypeFld.Access.Final,tp,i);
        if( !(tp instanceof TypeMemPtr) ) continue; // Not a pointer
        TypeObj to = ((TypeMem)tmem).ld((TypeMemPtr)tp).widen(); //
        // Are all the uses of parm compatible with this TMP?
        // Also, flag all used fields.
        if( bad_mem_use(parm, to) )
          continue;               // So bad usage

        TypeMemPtr arg = TypeMemPtr.make(BitsAlias.FULL,to); // Signature takes any alias but has sharper guts
        formals = formals.replace_fld(TypeFld.make(parm._name,arg,i));
        progress = true;
      }
      if( progress ) return formals;
    }

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
      case OP_FRESH:         // No value change
        if( bad_mem_use(use, to) ) return true;
        break;
      case OP_LOAD:
        if( !(to instanceof TypeStruct) ||
            ((LoadNode)use).find((TypeStruct)to)== null )
          return true;          // Did not find field
        break;
      case OP_STORE:
        if( ((StoreNode)use).rez()==n) break; // Storing as value is ok
        if( !(to instanceof TypeStruct) ||    // Address needs to find field
            ((StoreNode)use).find((TypeStruct)to)== null )
          return true;          // Did not find field
        break;
      case OP_CALL: break; // Argument pass-thru probably needs to check formals
      case OP_RET: break;  // Return pass-thru should be ok
      case OP_NEWSTR:
        TypeStruct formals = ((NewStrNode)use)._formals;
        Type formal = formals.fld_idx(use._defs.find(n))._t;
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
        if( use instanceof PrimNode.AddF64 ) return true;
        if( use instanceof PrimNode.AddI64 ) return true;
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
  private TypeStruct type_special( Node[] parms ) {
    if( !has_unknown_callers() ) return null; // Only overly-wide calls.
    TypeStruct formals = find_type_split(parms);
    if( formals == null ) return null; // No unresolved calls; no point in type-specialization
    //// Make a new function header with new signature
    //if( !formals.isa(_sig._formals) ) return null;    // Fails in error cases
    //return formals == _sig._formals ? null : formals; // Must see improvement
    throw unimpl();
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
    //for( Node use : ret._uses ) // Include all FunPtrs as part of body
    //  if( use instanceof FunPtrNode )
    //    body.push(use);
    work.add(ret);
    while( !work.isEmpty() ) {  // While have work
      Node n = work.pop();      // Get work
      if( n==null ) continue;   // Defs can be null
      // As a special case for H-M, always clone uses of nil constants.
      // These need private H-M variables to support polymorphic nil-typing.
      if( n instanceof ConNode && ((ConNode)n)._t==Type.XNIL ) freached.tset(n._uid);
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
    int call_indirect=0; // Count of calls to e.g. loads/args/parms
    int[] cnts = new int[OP_MAX];
    for( Node n : body ) {
      int op = n._op;           // opcode
      if( op == OP_CALL ) {     // Call-of-primitive?
        Node n1 = ((CallNode)n).fdx();
        if( !(n1._val instanceof TypeFunPtr) ) return -1; // Calling an unknown function, await GCP
        TypeFunPtr tfp = (TypeFunPtr)n1._val;
        if( tfp._fidxs.test(_fidx) ) self_recursive = true; // May be self-recursive
        //Node n2 = n1 instanceof UnOrFunPtrNode ? ((UnOrFunPtrNode)n1).funptr() : n1;
        //if( n2 instanceof FunPtrNode ) {
        //  FunPtrNode fpn = (FunPtrNode) n2;
        //  if( fpn.ret().rez() instanceof PrimNode )
        //    op = OP_PRIM;       // Treat as primitive for inlining purposes
        //} else
        //  call_indirect++;
        throw unimpl();
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
        cnts[OP_NEWOBJ]>2 ||   // Display and return is OK
        (cnts[OP_NEWOBJ]>1 && self_recursive) ||
        call_indirect > 0 )
      return -1;

    if( self_recursive ) return -1; // Await GCP & call-graph discovery before inlining self-recursive functions

    // Pick which input to inline.  Only based on having some constant inputs
    // right now.
    Node mem = parms[MEM_IDX];  // Memory, used to sharpen input ptrs
    int m=-1, mncons = -1;
    for( int i=has_unknown_callers() ? 2 : 1; i<_defs._len; i++ ) {
      Node call = in(i).in(0);
      if( !(call instanceof CallNode) ) continue; // Not well-formed
      if( ((CallNode)call).nargs() != nargs() ) continue; // Will not inline
      if( call._val == Type.ALL ) continue; // Otherwise in-error
      TypeFunPtr tfp = CallNode.ttfp(call._val);
      int fidx = tfp.fidxs().abit();
      if( fidx < 0 || BitsFun.is_parent(fidx) ) continue;    // Call must only target one fcn
      if( self_recursive && body.find(call)!=-1 ) continue; // Self-recursive; amounts to unrolling
      int ncon=0;
      // Count constant inputs on non-error paths
      for( int j=DSP_IDX; j<parms.length; j++ ) {
        ParmNode parm = (ParmNode)parms[j];
        if( parm != null ) {    // Some can be dead
          Type actual = parm.in(i).sharptr(mem.in(i));
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
    int oldfidx = fidx();
    FunNode fun = new FunNode(_name, BitsFun.new_fidx(oldfidx),_op_prec,_nargs);
    fun._bal_close = _bal_close;
    fun.pop();                  // Remove null added by RegionNode, will be added later

    // If type-splitting renumber the original as well; the original _fidx is
    // now a *class* of 2 fidxs.  Each FunNode fidx is only ever a constant, so
    // the original Fun becomes the other child fidx.  If size-splitting there
    // are no callers of the new fidx other than the call site.
    if( path == -1 ) {
      int newfidx = _fidx = BitsFun.new_fidx(oldfidx);
      FUNS.setX(newfidx,this);    // Track FunNode by fidx
      FUNS.clear(oldfidx);        // Old fidx no longer refers to a single FunNode
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
      Node ceproj = pop();
      CallNode call = (CallNode)ceproj.in(0); // Unhook without removal
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
      // FunPtr clones for path calls: always use the original Code, as the
      // path clone will be going away.
      if( n instanceof FunPtrNode && path >= 0 && path_call.fdx()!= n ) {
        c.add_def(n.in(0)); //
        Node dsp = map.get(n.in(1));
        c.add_def(dsp==null ? n.in(1) : dsp );

      } else {
        for( Node def : n._defs ) {
          Node newdef = map.get(def);// Map old to new
          c.add_def(newdef==null ? def : newdef);
        }
      }
    }

    // Keep around the old body, even as the FunPtrs get shuffled from Call to Call
    for( Node use : oldret._uses ) if( use instanceof FunPtrNode ) use.push();

    // Collect the old/new returns and funptrs and add to map also.  The old
    // Ret has a set (not 1!) of FunPtrs, one per unique Display.
    RetNode newret = (RetNode)map.get(oldret);
    newret._fidx = fun.fidx();
    if( path < 0 ) {            // Type split
      for( Node use : oldret._uses )
        if( use instanceof FunPtrNode ) { // Old-return FunPtrs; varies by Display & by internal/external
          // Make an Unresolved choice of the old and new functions, to be used
          // by everything except mutually recursive calls; including
          // external/top-level calls, storing to memory, external merges, etc.
          Node old_funptr = use;
          Node new_funptr = map.get(old_funptr);
          new_funptr.insert(old_funptr);
          new_funptr.xval(); // Build type so Unresolved can compute type
          //UnresolvedNode new_unr = new UnresolvedNode(null,new_funptr);
          //old_funptr.insert(new_unr);
          //new_unr.add_def(old_funptr);
          //new_unr._val = new_unr.value();
          throw unimpl();
        }
    } else {                         // Path split
      Node old_funptr = fptr(path_call.fdx()); // Funptr for the path split
      Node new_funptr = map.get(old_funptr);
      new_funptr.insert(old_funptr); // Make cloned recursive calls, call the old version not the new version
      TypeFunPtr ofptr = (TypeFunPtr) old_funptr._val;
      path_call.set_fdx(new_funptr); // Force new_funptr, will re-wire later
      TypeFunPtr nfptr = ofptr.make_from(BitsFun.make0(newret._fidx));
      path_call._val = CallNode.set_ttfp((TypeTuple) path_call._val,nfptr);
      //for( Node use : oldret._uses ) // Check extra FunPtrs are dead
      //  if( use instanceof FunPtrNode ) Env.GVN.add_dead(map.get(use));

    } // Else other funptr/displays on unrelated path, dead, can be ignored

    // For all aliases split in this pass, update in-node both old and new.
    // This changes their hash, and afterwards the keys cannot be looked up.
    for( Map.Entry<Node,Node> e : map.entrySet() )
      if( e.getKey() instanceof MemSplitNode )
        ((MemSplitNode)e.getKey()).split_alias(e.getValue(),aliases);

    // Wired Call Handling:
    if( zlen==2 ) {               // Not called by any unknown caller
      if( path < 0 ) {            // Type Split
        // Change the unknown caller parm types to match the new sig.  Default
        // memory includes the other half of alias splits, which might be
        // passed in from recursive calls.
        for( Node p : fun._uses )
          if( p instanceof ParmNode ) {
            ParmNode parm = (ParmNode)p;
            Node defx;
            if( parm._idx==0 ) defx = Node.con(TypeRPC.ALL_CALL);
            else if( parm._idx==MEM_IDX ) throw unimpl();
            else {
              //Type tx = fun.formal(parm._idx).simple_ptr();
              //defx = Node.con(tx);
              throw unimpl();
            }
            parm.set_def(1,defx);
          }
      } else                     // Path Split
        fun.set_def(1,Env.XCTRL);
    }

    // Put all new nodes into the GVN tables and worklist
    //boolean split_alias=false;
    for( Map.Entry<Node,Node> e : map.entrySet() ) {
      Node oo = e.getKey();     // Old node
      Node nn = e.getValue();   // New node
      Type nt = oo._val;        // Generally just copy type from original nodes
      //if( nn instanceof MrgProjNode ) { // Cloned allocations registers with default memory
      //  MrgProjNode nnrg = (MrgProjNode)nn;
      //  MrgProjNode oorg = (MrgProjNode)oo;
      //  //Env.DEFMEM.make_mem(nnrg.nnn()._alias,nnrg);
      //  //Env.DEFMEM.make_mem(oorg.nnn()._alias,oorg);
      //  //int oldalias = BitsAlias.parent(oorg.nnn()._alias);
      //  //Env.DEFMEM.set_def(oldalias,Env.XUSE); // Old alias is dead
      //  //Env.GVN.add_mono(oorg.nnn());
      //  //Env.GVN.add_flow_uses(oorg);
      //  //split_alias=true;
      //}
      if( nn instanceof FunPtrNode && (path==0 || path_call.fdx()==nn)) { // FunPtrs pick up the new fidx
        TypeFunPtr ofptr = (TypeFunPtr)nt;
        if( ofptr.fidx()==oldret._fidx )
          nt = ofptr.make_from(BitsFun.make0(newret._fidx));
      }
      nn._val = nt;             // Values
      nn._elock();              // In GVN table
    }
    //if( split_alias ) {
    //  //Env.DEFMEM.xval();
    //  throw unimpl();
    //}

    //// Eagerly lift any Unresolved types, so they quit propagating the parent
    //// (and both children) to all targets.
    //for( Node fptr : oldret._uses )
    //  if( fptr instanceof FunPtrNode )
    //    for( Node unr : fptr._uses )
    //      if( unr instanceof UnresolvedNode )
    //        //unr._val = unr.value();
    //        throw unimpl(); // Call xval?  But actually drop Unresolved?

    // Rewire all unwired calls.
    for( CallEpiNode cepi : unwireds ) {
      CallNode call = cepi.call();
      CallEpiNode cepi2 = (CallEpiNode)map.get(cepi);
      if( path < 0 ) {          // Type-split, wire both & resolve later
        BitsFun call_fidxs = ((TypeFunPtr) call.fdx()._val).fidxs();
        assert call_fidxs.test_recur(    fidx()) ;  cepi.wire1(call,this,oldret,false);
        if(    call_fidxs.test_recur(fun.fidx()) )  cepi.wire1(call, fun,newret,false);
        if( cepi2!=null ) {
          // Found an unwired call in original: musta been a recursive self-
          // call.  wire the clone, same as the original was wired, so the
          // clone keeps knowledge about its return type.
          CallNode call2 = cepi2.call();
          BitsFun call_fidxs2 = ((TypeFunPtr) call2.fdx()._val).fidxs();
          if(    call_fidxs2.test_recur(    fidx()) )  cepi2.wire1(call2,this,oldret,false);
          assert call_fidxs2.test_recur(fun.fidx()) ;  cepi2.wire1(call2, fun,newret,false);
        }
      } else {                  // Non-type split, wire left or right
        if( call==path_call ) cepi.wire1(call, fun,newret,false);
        else                  cepi.wire1(call,this,oldret,false);
        if( cepi2!=null && cepi2.call()!=path_call ) {
          CallNode call2 = cepi2.call();
          // Found an unwired call in original: musta been a recursive
          // self-call.  wire the clone, same as the original was wired, so the
          // clone keeps knowledge about its return type.
          //call2.set_fdx(call.fdx());
          cepi2.wire1(call2,this,oldret,false);
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
            ncepi.wire0(ncepi.call(),xxxret.fun(),false);
          }
        }
        // CEProjs from the Call never re-wire, as they are not uniquely
        // identified by input alone.  Other Projs DO rewire, if any target
        // function uses them.
        for( Node use : ncepi.call()._uses )
          if( use._uses._len==0 ) Env.GVN.add_dead(use);
      }
    }

    // Retype memory, so we can everywhere lift the split-alias parents "up and out".
    GVNGCM.retype_mem(aliases,this.parm(MEM_IDX), oldret, true);
    GVNGCM.retype_mem(aliases,fun .parm(MEM_IDX), newret, true);

    // Unhook the hooked FunPtrs
    for( Node use : oldret._uses ) if( use instanceof FunPtrNode ) GVNGCM.pop(GVNGCM.KEEP_ALIVE._defs._len);
  }

  // Compute value from inputs.  Simple meet over inputs.
  @Override public Type value() {
    // Will be an error eventually, but act like its executed so the trailing
    // EpilogNode gets visited during GCP
    if( is_prim() ) return Type.CTRL;
    if( in(0)==this ) return _defs._len>=2 ? val(1) : Type.XCTRL; // is_copy
    if( _defs._len==2 && in(1)==this ) return Type.XCTRL; // Dead self-loop
    int i = has_unknown_callers() && !is_unknown_alive() ? 2 : 1;
    for( ; i<_defs._len; i++ ) {
      Type c = val(i);
      if( c == Type.CTRL || c == Type.ALL ) return Type.CTRL; // Valid path
    }
    return Type.XCTRL;
  }

  // Funs get special treatment by the H-M algo.
  @Override public TV2 new_tvar( String alloc_site) { return null; }
  @Override public boolean unify( boolean test ) { return false; }

  // Nongenerative set for Hindly-Milner
  public void prep_nongen() {
    // Gather TV2s from parents
    Ary<TV2> tv2s = new Ary<>(TV2.class);

    // Gather the rest from my parms
    for( Node use : _uses )
      if( use instanceof ParmNode && use._tvar!=null )
        tv2s.push(use._tvar);
    _nongen = tv2s.asAry();
  }

  // True if this is a forward_ref
  public ParmNode parm( int idx ) {
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx==idx )
        return (ParmNode)use;
    return null;
  }
  public Node[] parms() {
    Node[] parms = new Node[nargs()];
    for( Node use : _uses )
      if( use instanceof ParmNode )
        parms[((ParmNode)use)._idx] = use;
    return parms;
  }
  public RetNode ret() {
    if( is_dead() ) return null;
    for( Node use : _uses )
      if( use instanceof RetNode && use._defs._len==5 && !((RetNode)use).is_copy() && ((RetNode)use).fun()==this )
        return (RetNode)use;
    return null;
  }
  // Returns first - not ALL - FunPtrs
  public FunPtrNode fptr() {
    RetNode ret = ret();
    if( ret==null ) return null;
    for( Node fptr : ret._uses )
      if( fptr instanceof FunPtrNode )
        return (FunPtrNode)fptr;
    return null;
  }
  // Returns matching FunPtr for a Calls FDX
  public FunPtrNode fptr(Node fdx) {
    FunPtrNode fptr=null;
    if( fdx instanceof FunPtrNode ) {
      fptr = (FunPtrNode)fdx;
    } else {
      assert fdx instanceof UnresolvedNode;
      for( Node fdx2 : fdx._defs )
        if( (fptr=(FunPtrNode)fdx2).fun()==this )
          break;
    }
    assert fptr.fun()==this;
    return fptr;
  }

  @Override public boolean equals(Object o) { return this==o; } // Only one
  @Override public Node is_copy(int idx) {
    if( len()==1 ) return in(0); // Collapsing
    return in(0)==this ? in(1) : null;
  }
  void set_is_copy() { set_def(0,this); Env.GVN.add_reduce_uses(this); }
}
