package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;

// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// null, same as a C2 Region.  Args 1+ point to the callers control.  Before
// GCP/opto arg 1 points to ALL_CTRL as the generic unknown worse-case caller.
// ALL_CTRL is removed just prior to GCP, the precise call-graph is discovered,
// and calls are directly wired to the FunNode as part of GCP.  After GCP the
// call-graph is known precisely and is explicit in the graph.
//
// FunNodes are finite in count and are unique densely numbered, see BitsFun.
//
// Pointing to the FunNode are ParmNodes which are also PhiNodes; one input
// path for each known caller.  Zero slot points to the FunNode.  Arg1 points
// to the generic unknown worse-case caller (a type-specific ConNode with
// worse-case legit bottom type).  ParmNodes merge all input path types (since
// they are a Phi), and the call "loses precision" for type inference there.
// Parm#0 and up (NOT the zero-slot but the zero idx) are the classic function
// arguments; Parm#-1 is for the RPC and Parm#-2 is for memory.
//
// The function body points to the FunNode and ParmNodes like C2.
//
// RetNode points to the return control, memory, value and RPC.  EpilogNode
// points to the RetNode and is typed as a TypeFunPtr.  The TFP is used as a
// 1st-class function pointer and is carried through the program like a normal
// value.  Direct Calls will point to the Epilog directly.
//
// Memory both is and is-not treated special: the function body flows memory
// through from the initial Parm to the Ret in the normal way.  However the
// incoming memory argument is specifically trimmed by the Call to only those
// aliases used by the function body (either read or write), and the Ret only
// returns those memories explicitly written.  All the other aliases are
// treated as "pass-through" and explicitly routed around the Fun/Ret by the
// Call/CallEpi pair.
//
public class FunNode extends RegionNode {
  public String _name;          // Optional for anon functions; can be set later via bind()
  public TypeFunPtr _tf;        // FIDX, arg & ret types
  public BitsAlias _closure_aliases;
  // Operator precedence; only set on top-level primitive wrappers.
  // -1 for normal non-operator functions and -2 for forward_decls.
  private final byte _op_prec;  // Operator precedence; only set on top-level primitive wrappers
  private byte _cnt_size_inlines; // Count of size-based inlines

  // Used to make the primitives at boot time
  public  FunNode(PrimNode prim) { this(prim._name,TypeFunPtr.make_new(prim._targs,prim._ret),prim.op_prec()); }
  public  FunNode(IntrinsicNewNode prim, Type ret) { this(prim._name,TypeFunPtr.make_new(prim._targs,ret),-1); }
  // Used to make copies when inlining/cloning function bodies
          FunNode(String name,TypeFunPtr tf) { this(name,tf,-1); }
  // Used to start an anonymous function in the Parser
  public  FunNode(Type[] ts) { this(null,TypeFunPtr.make_new(TypeStruct.make(ts),Type.SCALAR),-1); }
  // Used to forward-decl anon functions
          FunNode(String name) { this(name,TypeFunPtr.make_anon(),-2); add_def(Env.ALL_CTRL); }
  // Shared common constructor
  private FunNode(String name, TypeFunPtr tf, int op_prec) {
    super(OP_FUN);
    _name = name;
    assert tf.isa(TypeFunPtr.GENERIC_FUNPTR);
    assert TypeFunPtr.GENERIC_FUNPTR.dual().isa(tf);
    _tf = tf;
    _op_prec = (byte)op_prec;
    assert !tf.is_class();
    FUNS.setX(fidx(),this); // Track FunNode by fidx; assert single-bit fidxs
    // Stack of active closures this function can reference.
    _closure_aliases = Env.CLOSURES;
  }

  // Find FunNodes by fidx
  static Ary<FunNode> FUNS = new Ary<>(new FunNode[]{null,});
  public static FunNode find_fidx( int fidx ) { return fidx >= FUNS._len ? null : FUNS.at(fidx); }
  int fidx() { return _tf.fidx(); } // Asserts single-bit internally

  // Fast reset of parser state between calls to Exec
  static int PRIM_CNT;
  public static void init0() { PRIM_CNT = FUNS._len; }
  public static void reset_to_init0() {
    FUNS.set_len(PRIM_CNT);
    for( int i=2; i<PRIM_CNT; i++ ) {
      FunNode fun = FUNS.at(i);
      if( fun != null && fun.fidx() != i ) { // Cloned primitives get renumbered, so renumber back
        RetNode ret = fun.ret();
        fun._tf = fun._tf.make_fidx(i);
        ret._fidx = i;
      }
    }
  }

  // Short self name
  @Override String xstr() { return name(); }
  // Inline longer info
  @Override public String str() { return is_forward_ref() ? xstr() : _tf.str(null); }
  // Name from fidx alone
  private static String name( int fidx ) {
    FunNode fun = find_fidx(fidx);
    return fun == null ? ""+fidx : fun.name();
  }
  // Name from FunNode
  String name() {
    String name = _name==null ? "fun"+fidx() : _name;
    return is_forward_ref()
      ? "?"+name
      : (_op_prec >= 0 ? "{"+name+"}" : name+"={->}");
  }
  public boolean noinline() { return _name != null && _name.startsWith("noinline"); }

  // Can return nothing, or "name" or "[name0,name1,name2...]" or "[35]"
  public static SB names(BitsFun fidxs, SB sb ) {
    int fidx = fidxs.abit();
    if( fidx >= 0 ) return sb.p(name(fidx));
    int cnt=0;
    for( Integer ii : fidxs ) {
      if( ++cnt==5 ) break;
      sb.p(name(ii)).p(fidxs.above_center()?'+':',');
    }
    if( cnt>=5 ) sb.p("...");
    return sb;
  }

  // Debug only: make an attempt to bind name to a function
  public void bind( String tok ) {
    assert _name==null || _name.equals(tok); // Attempt to double-bind
    _name = tok;
  }

  // Never inline with a nested function
  @Override Node copy(boolean copy_edges, CallEpiNode unused, GVNGCM gvn) { throw AA.unimpl(); }

  // True if may have future unknown callers.
  private boolean has_unknown_callers() { return _defs._len > 1 && in(1) == Env.ALL_CTRL; }
  // Argument type
  Type targ(int idx) {
    return idx == -1 ? TypeRPC.ALL_CALL :
      (idx == -2 ? TypeMem.MEM : _tf.arg(idx));
  }
  int nargs() { return _tf._args._ts.length; }
  // FunNode lost a use.  If lost a formal argument (a Parm), visit all wired
  // Call nodes and drop the corresponding actual argument.  Visit all unwired
  // calls to see if they will wire, now that an arg has died.
  @Override public boolean ideal_impacted_by_losing_uses(GVNGCM gvn, Node dead) {
    if( dead instanceof ParmNode ) {
      RetNode ret = ret();
      if( ret != null ) {
        FunPtrNode fptr = ret.funptr();
        if( fptr != null ) {
          for( Node call : fptr._uses )
            if( call instanceof CallNode )
              for( Node cepi : call._uses )
                gvn.add_work(cepi); // Might wire a call, the dead arg was in error
        }
      }
    }
    return true;
  }

  // ----
  @Override public Node ideal(GVNGCM gvn) {
    // Generic Region ideal
    Node n = super.ideal(gvn);
    if( n!=null ) return n;

    // If no trailing RetNode and hence no FunPtr... function is uncallable
    // from the unknown caller.
    RetNode ret = ret();
    if( has_unknown_callers() && ret == null && gvn._opt_mode == 1 ) { // Dead after construction?
      set_def(1,gvn.con(Type.XCTRL),gvn); // Kill unknown caller
      return this;
    }

    if( gvn._small_work ) { // Only doing small-work now
      gvn.add_work2(this);  // Maybe want to inline later
      return null;
    }

    // Type-specialize as-needed
    if( is_forward_ref() ) return null;
    ParmNode rpc_parm = rpc();
    if( rpc_parm == null ) return null; // Single caller const-folds the RPC, but also inlines in CallNode
    ParmNode[] parms = new ParmNode[nargs()];
    if( split_callers_gather(gvn,parms) == null ) return null;

    // Gather callers of this function being cloned.  Also does a decent sanity
    // check, so done before the split-choice heuristics.
    assert _defs._len == ret._uses._len+(has_unknown_callers() ? 1 : 0); // Every input path is wired to an output path
    CGEdge[] cgedges = new CGEdge[_defs._len];
    for( int i=1; i<_defs._len; i++ ) {
      assert gvn.type(in(i))==Type.CTRL; // Dead paths already removed
      cgedges[i] = new CGEdge(gvn, rpc_parm,i,ret);
    }

    // Look for appropriate type-specialize callers
    TypeStruct args = type_special(gvn, parms);
    int path = -1;              // Paths will split according to type
    if( args == null ) {        // No type-specialization to do
      args = _tf._args;         // Use old args
      if( _cnt_size_inlines >= 10 ) return null;
      // Large code-expansion allowed; can inline for other reasons
      path = split_size(gvn,ret,parms);
      if( path == -1 ) return null;
      if( noinline() ) return null;
      if( fidx() >= PRIM_CNT ) _cnt_size_inlines++; // Disallow infinite size-inlining of recursive non-primitives
    }
    // Split the callers according to the new 'fun'.
    FunNode fun = make_new_fun(gvn, ret, args);
    return split_callers(gvn,parms,ret,fun,cgedges,path);
  }

  // Gather the ParmNodes into an array.  Return null if any input path is dead
  // (would rather fold away dead paths before inlining).  Return null if there
  // is only 1 path.  Return null if any actuals are not formals.
  private RetNode split_callers_gather( GVNGCM gvn, ParmNode[] parms ) {
    for( int i=1; i<_defs._len; i++ ) if( gvn.type(in(i))==Type.XCTRL ) return null;
    if( _defs._len <= 2 ) return null; // No need to split callers if only 1

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
      if( parm != null )         //   (some can be dead)
        for( Node call : parm._uses ) // See if a parm-user needs a type-specialization split
          if( call instanceof CallNode &&
              ((CallNode)call).fun() instanceof UnresolvedNode ) { // Call overload not resolved
            Type t0 = gvn.type(parm.in(1));            // Generic type in slot#1
            for( int i=2; i<parm._defs._len; i++ ) {   // For all other inputs
              Type tp = gvn.type(parm.in(i));
              if( tp.above_center() ) continue;        // This parm input is in-error
              Type ti = tp.widen();                    // Get the widen'd type
              assert ti.isa(t0);                       // Must be isa-generic type, or else type-error
              if( ti != t0 ) return i; // Sharpens?  Then splitting here should help
            }
            // Else no split will help this call, look for other calls to help
          }
    return -1; // No unresolved calls; no point in type-specialization
  }

  private Type[] find_type_split( GVNGCM gvn, ParmNode[] parms ) {
    assert has_unknown_callers(); // Only overly-wide calls.
    // Look for splitting to help an Unresolved Call.
    int idx = find_type_split_index(gvn,parms);
    if( idx != -1 ) {           // Found; split along a specific input path using widened types
      Type[] sig = new Type[parms.length];
      for( int i=0; i<parms.length; i++ )
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
    if( !tp.isa(TypeStruct.GENERIC) ) return tp;
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
    TypeStruct args = TypeStruct.make(sig);
    assert args.isa(_tf._args);
    return args == _tf._args ? null : args; // Must see improvement
  }

  // Split a single-use copy (e.g. fully inline) if the function is "small
  // enough".  Include anything with just a handful of primitives, or a single
  // call, possible with a single if.
  private int split_size( GVNGCM gvn, RetNode ret, ParmNode[] parms ) {
    if( _defs._len <= 1 ) return -1; // No need to split callers if only 2
    BitSet recursive = new BitSet();    // Heuristic to limit unrolling recursive methods

    // Count function body size.  Requires walking the function body and
    // counting opcodes.  Some opcodes are ignored, because they manage
    // dependencies but make no code.
    int[] cnts = new int[OP_MAX];
    VBitSet bs = new VBitSet();
    Ary<Node> work = new Ary<>(new Node[1],0);
    work.add(this);             // Prime worklist
    while( work._len > 0 ) {    // While have work
      Node n = work.pop();      // Get work
      if( bs.tset(n._uid) ) continue; // Already visited?
      int op = n._op;           // opcode
      if( op == OP_FUN  && n       != this ) continue; // Call to other function, not part of inlining
      if( op == OP_PARM && n.in(0) != this ) continue; // Arg  to other function, not part of inlining
      if( op == OP_RET && ((RetNode)n).is_copy() ) continue; // Dead function ptr
      if( n != ret )            // Except for the RetNode
        work.addAll(n._uses);   // Visit all uses also
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
    int m=-1, mncons = -1;
    for( int i=has_unknown_callers() ? 2 : 1; i<_defs._len; i++ ) {
      int ncon=0;
      for( ParmNode parm : parms )
        if( parm != null ) {    // Some can be dead
          Type t = gvn.type(parm.in(i));
          if( !t.isa(targ(parm._idx)) ) // Path is in-error?
            { ncon = -2; break; } // This path is in-error, cannot inline even if small & constants
          if( t.is_con() ) ncon++; // Count constants along each path
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

  private FunNode make_new_fun(GVNGCM gvn, RetNode ret, TypeStruct new_args) {
    // Make a prototype new function header split from the original.
    int oldfidx = fidx();
    FunNode fun = new FunNode(_name,_tf.make_new_fidx(oldfidx,new_args));
    fun.pop();                  // Remove null added by RegionNode, will be added later
    // Renumber the original as well; the original _fidx is now a *class* of 2
    // fidxs.  Each FunNode fidx is only ever a constant, so the original Fun
    // becomes the other child fidx.
    _tf = _tf.make_new_fidx(oldfidx,_tf._args);
    int newfidx = fidx();       // New fidx for 'this'
    FUNS.setX(newfidx,this);    // Track FunNode by fidx
    ret._fidx = newfidx;        // Renumber in the old RetNode
    FunPtrNode old_fptr = ret.funptr();
    gvn.setype(old_fptr,_tf);   // Renumber in old FunPtrNode
    gvn.add_work(ret);
    gvn.add_work(old_fptr);
    return fun;
  }

  // ---------------------------------------------------------------------------
  // Clone the function body, and split the callers of 'this' into 2 sets; one
  // for the old and one for the new body.  The new function may have a more
  // refined signature, and perhaps no unknown callers.
  private Node split_callers( GVNGCM gvn, ParmNode[] parms, RetNode oldret, FunNode fun, CGEdge[] cgedges, int path) {
    // Strip out all wired calls to this function.  All will re-resolve later.
    for( CGEdge cg : cgedges )
      if( cg != null && cg._cepi != null )
        gvn.remove(cg._cepi,cg._cepi._defs.find(oldret));
    // Strip out all paths to this function.
    final int lim = has_unknown_callers() ? 2 : 1;
    while( lim < _defs._len ) {
      pop();
      for( Node parm : _uses )
        if( parm instanceof ParmNode ) {
          Type oldt = gvn.unreg(parm);
          parm.pop();
          gvn.rereg(parm,oldt);
        }
    }
    // If inlining into one path, get the CallEpi for the call site.  Used at
    // least to get a better error message for trivial inlined constructors.
    CallEpiNode cepi = path >= 0 ? cgedges[path]._cepi : null;
    // If inlining inside another function, try to put that function on the
    // worklist, to see if it inlines also.
    if( cepi != null ) {
      Node outer_fun = cepi.walk_dom_last(n -> n instanceof FunNode);
      if( outer_fun != null ) gvn.add_work(outer_fun);
    }

    // Map from old to cloned function body
    HashMap<Node,Node> map = new HashMap<>();
    // Collect aliases that are cloning.
    BitSet aliases = new BitSet();
    // Clone the function body
    map.put(this,fun);
    Ary<Node> work = new Ary<>(new Node[1],0);
    work.addAll(_uses);                  // Prime worklist
    while( work._len > 0 ) {             // While have work
      Node n = work.pop();               // Get work
      if( map.get(n) != null ) continue; // Already visited?
      if( n == oldret ) continue;        // Do not walk past the RetNode
      int op = n._op;                    // opcode
      if( op == OP_FUN  && n       != this ) continue; // Call to other function, not part of inlining
      if( op == OP_PARM && n.in(0) != this ) continue; // Arg  to other function, not part of inlining
      if( n instanceof NewNode ) aliases.set(((NewNode)n)._alias);
      map.put(n,n.copy(false,cepi,gvn)); // Make a blank copy with no edges and map from old to new
      work.addAll(n._uses);   // Visit all uses also
    }

    // Collect the old/new funptrs and add to map also.
    RetNode newret = (RetNode)oldret.copy(false,cepi,gvn);
    newret._fidx = fun.fidx();
    map.put(oldret,newret);
    FunPtrNode old_funptr = oldret.funptr();
    FunPtrNode new_funptr = (FunPtrNode)old_funptr.copy(false,cepi,gvn);
    new_funptr.add_def(newret);
    old_funptr.keep(); // Keep around; do not kill last use before the clone is done

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
      e.getKey().update_alias(e.getValue(),aliases,gvn);
    // We kept the unknown caller path on 'this', and then copied it to 'fun'.
    // But if inlining along a specific path, only that path should be present.
    // Kill the unknown_caller path.
    if( path >= 0 && has_unknown_callers() )
      fun.set_def(1,gvn.con(Type.XCTRL),gvn);
    else if( path < 0 && has_unknown_callers() ) {
      // Change the unknown caller parm types to match the new sig
      for( Node parm : fun._uses )
        if( parm instanceof ParmNode )
          parm.set_def(1,gvn.con(fun.targ(((ParmNode)parm)._idx)),gvn);
    }

    // Make an Unresolved choice of the old and new functions, to be used by
    // non-application uses.  E.g., passing a unresolved function pointer to a
    // 'map()' call.
    gvn.setype(new_funptr,new_funptr.value(gvn));
    UnresolvedNode new_unr = null;
    if( path < 0 ) {
      new_unr = (UnresolvedNode)gvn.xform(new UnresolvedNode(null,old_funptr,new_funptr));
      for( int i=0; i<old_funptr._uses._len; i++ ) {
        Node use = old_funptr._uses.at(i);
        if( use == new_unr ) continue;
        // Find the use idx; skip CallNode.fun() uses as these will be wired
        // correctly shortly.
        for( int idx=0; idx < use._defs._len; idx++ )
          if( use.in(idx) == old_funptr && !(use instanceof CallNode && idx==1) )
            { gvn.set_def_reg(use,idx,new_unr); i--; break; }
      }
      gvn.add_work(new_unr);
      new_unr.keep();
    }

    // Put all new nodes into the GVN tables and worklist
    for( Map.Entry<Node,Node> e : map.entrySet() ) {
      Node nn = e.getValue();         // New node
      Type ot = gvn.type(e.getKey()); // Generally just copy type from original nodes
      if( nn instanceof ParmNode && nn.in(0) == fun ) {  // Leading edge ParmNodes
        int idx = ((ParmNode)nn)._idx; // Update default type to match signature
        if( idx == -1 ) ot = nn.all_type(); // Except the new RPC, which has new callers
      } else if( nn == new_funptr ) {
        ot = fun._tf;           // New TFP for the new FunPtr
      } else if( nn instanceof CallEpiNode ) { // Old calls might be wired, new calls need to re-wire
        while( ((CallEpiNode)nn).nwired() > 0 ) nn.pop();
      }
      gvn.rereg(nn,ot);
    }
    gvn.add_work(this);
    gvn.add_work(fun );

    // Rewire all previously wired calls
    for( int e=has_unknown_callers() ? 2 : 1; e<cgedges.length; e++ ) {
      CGEdge cg = cgedges[e];
      CallNode call = cg.call();
      CallNode newcall = (CallNode)map.get(call); // Fetch before changing edges, hence map hash
      FunPtrNode fp;
      if( path < 0 ) {          // Type-split, each call site resolves left or right
        call.set_fun_reg(new_unr,gvn); // Unresolved; need to resolve
        fp = old_funptr;
        // Recompute path choice, as when we computed the new type sig.
        for( ParmNode parm : parms ) // For all parms
          if( parm != null ) {       //   (some can be dead)
            Type tp = gvn.type(call.arg(parm._idx)); // Specific path type
            if( !tp.isa(fun.targ(parm._idx)) || // If this path cannot use the sharper sig
                tp.above_center() )             // Or path is in-error
              { fp = old_funptr; break; } // Take the old, more generic version
            if( tp.widen() != targ(parm._idx) ) // Even widened, path is more specific than the generic
              fp = new_funptr;  // Then take it, but check remaining paths
          }
      } else {                  // Fixed inline path, choice already made
        fp = path==e ? new_funptr : old_funptr;
      }
      // Rewire all previously wired calls
      call.set_fun_reg(fp,gvn);
      gvn.setype(call,call.value(gvn));
      gvn.unreg(cg._cepi);
      cg._cepi.wire(gvn,call,fp == old_funptr ? this : fun, fp == old_funptr ? oldret : newret);
      gvn.rereg(cg._cepi,cg._cepi.value(gvn));
      // If we cloned a recursive call, it also needs updating but can resolve
      // and wire like any other new call.
      if( newcall != null ) {
        newcall.set_fun_reg(path < 0 ? new_unr : old_funptr, gvn);
        gvn.setype(newcall,newcall.value(gvn));
      }
    }
    // 'this' gets re-registered during the re-wiring process, blowing the
    // standard ideal() invariant.
    gvn.unreg(this);

    if( new_unr != null ) new_unr.unkeep(gvn);
    old_funptr.unkeep(gvn);
    // TODO: This fixup shouldn't be here, since old_funptr can go dead at any
    // time.  Anytime a FunPtrNode goes dead, there are NO uses which lead to
    // calls, unknown or not.
    if( old_funptr.is_dead() && !is_dead() && has_unknown_callers() )
      set_def(1,gvn.con(Type.XCTRL),gvn);

    return this;
  }

  // Compute value from inputs.  Simple meet over inputs.
  @Override public Type value(GVNGCM gvn) {
    // Will be an error eventually, but act like its executed so the trailing
    // EpilogNode gets visited during GCP
    if( is_forward_ref() ) return Type.CTRL;
    return super.value(gvn);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _op_prec==-2; }
  ParmNode parm( int idx ) {
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx==idx )
        return (ParmNode)use;
    return null;
  }
  public ParmNode rpc() { return parm(-1); }
  public RetNode ret() {
    for( Node use : _uses )
      if( use instanceof RetNode && !((RetNode)use).is_copy() )
        return (RetNode)use;
    return null;
  }

  @Override public int hashCode() { return super.hashCode()+_tf.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof FunNode) ) return false;
    FunNode fun = (FunNode)o;
    return _tf == fun._tf;
  }
  @Override public byte op_prec() { return _op_prec; }

  // Small/cheap holder for a call-graph edge
  private static class CGEdge {
    final CallEpiNode _cepi;    // Call epilog.
    final int _ridx;            // Return index edge, or -1 if not wired
    final ParmNode _rpc;        // RPC parm, or null if not wired
    final int _path;            // FunNode input path, if wired
    final TypeRPC _trpc;        // Type of RPCNode, matches call._rpc

    // Build a CG edge from a FunNode and input path
    CGEdge( GVNGCM gvn, ParmNode rpc_parm, int path, RetNode ret ) {
      _path = path;
      _rpc  = rpc_parm;         // The ParmNode
      _trpc = (TypeRPC)gvn.type(rpc_parm.in(path));
      if( _trpc != TypeRPC.ALL_CALL ) {
        int rpc = _trpc.rpc();    // The RPC#
        for( Node cepi : ret._uses ) {
          if( cepi instanceof CallEpiNode &&
              ((CallEpiNode)cepi).call()._rpc == rpc ) {
            _cepi = (CallEpiNode)cepi;
            _ridx = cepi._defs.find(ret);
            assert _ridx != -1;       // Must find, since wired
            return;
          }
        }
      }
      // Unknown caller path
      _cepi = null;  _ridx = -1;
    }
    CallNode call() { return _cepi.call(); }
  }
}
