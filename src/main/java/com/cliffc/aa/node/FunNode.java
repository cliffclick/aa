package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

import java.util.BitSet;
import java.util.HashMap;

// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// null, same as a C2 Region.  Args 1+ point to callers; Arg 1 points to Scope
// as the generic unknown worse-case caller; This can be removed once no more
// callers can appear after parsing.  Each unique call-site to a function gets
// a new path to the FunNode.
//
// FunNodes are finite in count and can be unique densely numbered.
//
// Pointing to the FunNode are ParmNodes which are also PhiNodes; one input
// path for each known caller.  Zero slot points to the FunNode.  Arg1 points
// to the generic unknown worse-case caller (a type-specific ConNode with
// worse-case legit bottom type).  The collection of these ConNodes can share
// TypeVars to structurally type the inputs.  ParmNodes merge all input path
// types (since they are a Phi), and the call "loses precision" for type
// inference there.
//
// The function body points to the FunNode and ParmNodes like C2.
//
// EpilogNode is different from C2s RetNode, to support precise function type
// inference.  Epilogs point to the return control, return value, RPC and the
// original FunNode; its type is a control Tuple, similar to IfNodes.  Pointing
// to the Epilog are RPCNodes with call-site indices; they carry the control-
// out of the function for their call-site.  While there is a single Epilog for
// all call-sites, Calls can "peek through" to see the function body learning
// the incoming args come from a known input path.
// 
// Results come from CastNodes, which up-cast the merged function results back
// to the call-site specific type - this is where the precision loss are
// ParmNodes is regained.  CastNodes point to the original call-site control
// path and the function result.

// Example: FunNode "map" is called with type args A[] and A->B and returns
// type B[]; at one site its "int[]" and "int->str" and at another site its
// "flt[]" and "flt->int" args.  The Epilog merges results to be "SCALAR[]".
// The Cast#1 upcasts its value to "str[]", and Cast#2 upcasts its value to
// "int[]".
// 
//  0 Scope...               -- Call site#1 control
//  1 Con_TV#C (really A[] ) -- Call site#1 arg#1
//  2 Con_TV#D (really A->B) -- Call site#1 arg#2
//  3 Ctrl callsite 2        -- Call site#2 control
//  4 arg#int[]              -- Call site#2 arg#1  
//  5 arg#int->str           -- Call site#2 arg#2  
//  6 Ctrl callsite 3        -- Call site#3 control
//  7 arg#flt[]              -- Call site#3 arg#1  
//  8 arg#flt->int           -- Call site#3 arg#2  
//  9 Fun _ 0 3 6
// 10 ParmX 9 1 4 7  -- meet of A[] , int[]   , flt[]
// 11 ParmX 9 2 5 8  -- meet of A->B, int->str, flt->int
// -- function body, uses 9 10 11
// 12 function body control
// 13 function body return value
// -- function ends
// 14 Epilog 12 13 9 {A[] {A -> B} -> B[]}
// 15 Proj#1 14            -- Return path  for unknown caller in slot 1
// 16 Cast#1 0 13#SCALAR[] -- Return value for unknown caller in slot 1
// 16 Proj#2 14            -- Return path  for caller {int[] {int -> str} -> str[]}
// 17 Cast#2 3 13#flt[]    -- Return value for caller {int[] {int -> str} -> str[]}
// 18 Proj#3 14            -- Return path  for caller {flt[] {flt -> int} -> int[]}
// 19 Cast#3 6 13#int[]    -- Return value for caller {flt[] {flt -> int} -> int[]}
//
// The Parser will use the Env to point to the RetNode to create more callers
// as parsing continues.  The RetNode is what is passed about for a "function
// pointer".
public class FunNode extends RegionNode {
  private static int CNT=1; // Function index; -1 for 'all' and 0 for 'any'
  public final TypeFun _tf; // Worse-case correct type
  private final byte _op_prec;// Operator precedence; only set top-level primitive wrappers
  // Used to make the primitives at boot time
  public FunNode(Node scope, PrimNode prim) { this(scope,TypeFun.make(prim._targs,prim._ret,CNT++),prim.op_prec(),prim._name); }
  // Used to make copies when inlining/cloning function bodies
  private FunNode(Node scope, TypeTuple ts, Type ret, String name) { this(scope,TypeFun.make(ts,ret,CNT++),-1,name); }
  // Used to start an anonymous function in the Parser
  public FunNode(int nargs, Node scope) { this(scope,TypeFun.any(nargs,CNT++),-1,null); }
  // Used to forward-decl anon functions
  FunNode(Node scope, String name) { this(scope,TypeFun.make_forward_ref(CNT),-1,name); }
  // Shared common constructor
  private FunNode(Node scope, TypeFun tf, int op_prec, String name) {
    super(OP_FUN);
    if( scope != null ) add_def(scope);
    _tf = tf;
    _op_prec = (byte)op_prec;
    if( name != null ) bind(name);
  }

  // Fast reset of parser state between calls to Exec
  private static int PRIM_CNT;
  public static void init0() { PRIM_CNT=CNT; }
  public static void reset_to_init0() { CNT = PRIM_CNT; NAMES.set_len(PRIM_CNT); }

  @Override String xstr() { return _tf.toString(); }
  @Override String str() { return names(_tf._fidxs,new SB()).toString(); }
  // Debug only: make an attempt to bind name to a function
  private static Ary<String> NAMES = new Ary<>(new String[1],0);
  public void bind(String tok) {
    int fidx = _tf.fidx();
    String name = NAMES.atX(fidx);
    assert name==null || name.equals(tok); // Attempt to double-bind
    NAMES.setX(fidx,tok);
  }
  // Can return nothing, or "name" or "{name0,name1,name2...}"
  public static SB names(Bits fidxs, SB sb ) {
    int fidx = fidxs.abit();
    if( fidx > 0 ) return name(fidx,sb);
    sb.p('{');
    int cnt=0;
    for( Integer ii : fidxs ) {
      if( ++cnt==3 ) break;
      name(ii,sb).p(',');
    }
    if( cnt>=3 || fidxs.abit() < 0 ) sb.p("...");
    sb.p('}');
    return sb;
  }
  private static SB name( int i, SB sb ) {
    String name = NAMES.atX(i);
    return sb.p(name==null ? "{"+Integer.toString(i)+"}" : name);
  }
  public String name() { return name(_tf.fidx()); }
  public static String name(int fidx) { return NAMES.atX(fidx); }

  @Override Node copy() {
    throw AA.unimpl();          // Gotta make a new FIDX
  }
  
  // FunNodes can "discover" callers if the function constant exists in the
  // program anywhere (since, during execution (or optimizations) it may arrive
  // at a CallNode and initiate a new call to the function).  Until all callers
  // are accounted for, the FunNode keeps slot1 reserved with the most
  // conservative allowed arguments, under the assumption a as-yet-detected
  // caller will call with such arguments.  This is a quick check to detect
  // may-have-more-callers.
  private boolean _all_callers_known;
  boolean callers_known(GVNGCM gvn) {
    if( _all_callers_known ) return _all_callers_known; // Once true, always true
    if( _tf.is_forward_ref() || (at(1) instanceof ScopeNode) ) return false;
    return (_all_callers_known=true);
  }


  // ----
  @Override public Node ideal(GVNGCM gvn) {
    Node n = split_callers(gvn);
    if( n != null ) return n;

    // Else generic Region ideal
    return ideal(gvn,!callers_known(gvn));
  }

  private Node split_callers( GVNGCM gvn ) {
    // Bail if there are any dead paths; RegionNode ideal will clean out
    for( int i=1; i<_defs._len; i++ ) if( gvn.type(at(i))==Type.XCTRL ) return null;
    if( _defs._len <= 2 ) return null; // No need to split callers if only 1

    // Gather the ParmNodes and the EpilogNode.  Ignore other (control) uses
    int nargs = _tf._ts._ts.length;
    ParmNode[] parms = new ParmNode[nargs];
    ParmNode rpc = null;
    EpilogNode epi = null;
    for( Node use : _uses )
      if( use instanceof ParmNode ) {
        ParmNode parm = (ParmNode)use;
        if( parm._idx == -1 ) rpc = parm;
        else parms[parm._idx] = parm;
      } else if( use instanceof EpilogNode ) { assert epi==null || epi==use; epi = (EpilogNode)use; }

    // Make a clone of the original function to split the callers.  Done for
    // e.g. primitive type-specialization or for tiny functions.
    FunNode fun =   split_callers_heuristic(gvn,parms,epi);
    return fun==null ? null : split_callers(gvn,rpc  ,epi,fun);
  }
  
  // General heuristic for splitting the many callers of this function into
  // groups with a private function body.  Can be split to refine types
  // (e.g. primitive int math vs primitive float math), or to allow
  // constant-prop for some args, or for tiny size.
  private FunNode split_callers_heuristic( GVNGCM gvn, ParmNode[] parms, EpilogNode epi ) {
    // Split for tiny body
    FunNode fun0 = split_size(gvn,epi);
    if( fun0 != null ) return fun0;

    // Split for primitive type specialization
    FunNode fun1 = type_special(gvn,parms);
    if( fun1 != null ) return fun1;

    return null;                // No splitting callers
  }

  // Split a single-use copy (e.g. fully inline) if the function is "small
  // enough".  Include anything with just a handful of primitives, or a single
  // call, possible with a single if.
  private FunNode split_size( GVNGCM gvn, EpilogNode epi ) {
    int[] cnts = new int[OP_MAX];
    BitSet bs = new BitSet();
    Ary<Node> work = new Ary<>(new Node[1],0);
    work.add(this);             // Prime worklist
    while( work._len > 0 ) {    // While have work
      Node n = work.pop();      // Get work
      if( bs.get(n._uid) ) continue; // Already visited?
      if( n != epi )            // Except for the Epilog
        work.addAll(n._uses);   // Visit all uses also
      bs.set(n._uid);           // Flag as visited
      int op = n._op;           // opcode
      if( op==OP_CALL ) {       // Call-of-primitive?
        EpilogNode x = (EpilogNode)(n.at(1) instanceof UnresolvedNode ? n.at(1).at(0) : n.at(1));
        if( x.val() instanceof PrimNode )
          op = OP_PRIM;         // Treat as primitive for inlining purposes
      }
      cnts[op]++;               // Histogram ops
    }
    assert cnts[OP_FUN]==1 && cnts[OP_EPI]==1;
    assert cnts[OP_SCOPE]==0 && cnts[OP_TMP]==0;
    assert cnts[OP_REGION] <= cnts[OP_IF];
    // Specifically ignoring constants, errors, parms, phis, rpcs, types,
    // unresolved, and casts.  These all track & control values, but actually
    // do not generate any code.
    if( cnts[OP_CALL] > 1 || // Careful inlining more calls; leads to exponential growth
        cnts[OP_IF  ] > 1 || // Allow some trivial filtering to inline
        cnts[OP_PRIM] > 6 )  // Allow small-ish primitive counts to inline
      return null;
    
    // Make a prototype new function header.  No generic unknown caller
    // in slot 1, only slot 2.
    Node top = gvn.con(Type.XCTRL);
    FunNode fun = new FunNode(top,_tf._ts,_tf._ret,name());
    fun._all_callers_known=true; // private split always
    fun.add_def(at(2));
    for( int i=3; i<_defs._len; i++ ) fun.add_def(top);
    return fun;
  }

  // Look for type-specialization inlining.  If any ParmNode has an unresolved
  // Call user, then we'd like to make a clone of the function body (at least
  // up to getting all the function TypeUnions to clear out).  The specialized
  // code uses generalized versions of the arguments, where we only specialize
  // on arguments that help immediately.
  private FunNode type_special( GVNGCM gvn, ParmNode[] parms ) {
    // Visit all ParmNodes, looking for unresolved call uses
    boolean any_unr=false;
    for( ParmNode parm : parms )
      for( Node call : parm._uses )
        if( call instanceof CallNode &&
            (gvn.type(call.at(1)) instanceof TypeUnion || // Call overload not resolved
             gvn.type(call      ) instanceof TypeErr ||   // Call result is an error (arg mismatch)
             ((TypeTuple)gvn.type(call)).at(1) instanceof TypeErr) ) { // Call result is an error (arg mismatch)
          any_unr = true; break;
        }
    if( !any_unr ) return null; // No unresolved calls; no point in type-specialization

    // TODO: Split with a known caller in slot 1
    if( !(at(1) instanceof ScopeNode) )
      return null; // Untested: Slot 1 is not the generic unparsed caller

    // If Parm has unresolved calls, we want to type-specialize on its
    // arguments.  Call-site #1 is the most generic call site for the parser
    // (all Scalar args).  Peel out 2nd call-site args and generalize them.
    Type[] sig = new Type[parms.length];
    for( int i=0; i<parms.length; i++ )
      sig[i] = gvn.type(parms[i].at(2)).widen();
    // Make a new function header with new signature
    TypeTuple ts = TypeTuple.make(Type.XSCALAR,1.0,sig);
    assert ts.isa(_tf._ts);
    if( ts == _tf._ts ) return null; // No improvement for further splitting
    // Make a prototype new function header.  Clone the generic unknown caller in slot 1.  
    FunNode fun = new FunNode(at(1),ts,_tf._ret,name());
    // Look at remaining paths and decide if they split or stay
    for( int j=2; j<_defs._len; j++ ) {
      boolean split=true;
      for( int i=0; i<parms.length; i++ )
        split &= gvn.type(parms[i].at(j)).widen().isa(sig[i]);
      fun.add_def(split ? at(j) : gvn.con(Type.XCTRL));
    }
    // TODO: Install in ScopeNode for future finding
    fun._all_callers_known=true; // currently not exposing to further calls
    return fun;
  }

  // Clone the function body, and split the callers of 'this' into 2 sets; one
  // for the old and one for the new body.  The new function may have a more
  // refined signature, and perhaps no unknown callers.  
  private Node split_callers(GVNGCM gvn, ParmNode rpc_parm, EpilogNode epi, FunNode fun) {
    // Clone the function body
    HashMap<Node,Node> map = new HashMap<>();
    Ary<Node> work = new Ary<>(new Node[1],0);
    map.put(this,fun);
    work.addAll(_uses);         // Prime worklist
    while( work._len > 0 ) {    // While have work
      Node n = work.pop();      // Get work
      if( map.get(n) != null ) continue; // Already visited?
      assert n._uid < fun._uid; // Recursive calls will call 'fun' directly
      assert n.at(0)!=epi && (n._defs._len<=1 || n.at(1)!= epi || n instanceof CallNode); // Do not walk past epilog
      if( n != epi )           // Except for the Epilog
        work.addAll(n._uses);  // Visit all uses also
      map.put(n,n.copy()); // Make a blank copy with no edges and map from old to new
    }

    // TODO: Split with a known caller in slot 1
    if( !(at(1) instanceof ScopeNode) )  throw AA.unimpl(); // Untested: Slot 1 is not the generic unparsed caller
    if( ((ScopeNode)at(1)).get(name()) !=null )
      throw AA.unimpl(); // need to repoint the scope
    Node any = gvn.con(Type.XCTRL);
    Node newepi = map.get(epi);
    Node new_unr = epi;
    // Are we making a type-specialized copy, that can/should be found by same-typed users?
    // Or are we cloning a private copy just for this call-site?
    if( fun.at(1) != any ) {
      // All uses now get to select either the old or new (type-specific) copy.
      EpilogNode xxxepi = epi.copy();
      for( Node def : epi._defs ) xxxepi.add_def(def);
      gvn.init(xxxepi);
      new_unr = new UnresolvedNode();
      new_unr.add_def(xxxepi);
      new_unr.add_def(newepi);
      gvn.init(new_unr);
    }

    // Fill in edges.  New Nodes point to New instead of Old; everybody
    // shares old nodes not in the function (and not cloned).  The
    // FunNode & Parms only get the matching slice of args.
    for( Node n : map.keySet() ) {
      Node c = map.get(n);
      if( n instanceof ParmNode && n.at(0) == this ) {  // Leading edge ParmNodes
        c.add_def(map.get(n.at(0))); // Control
        int idx = ((ParmNode)n)._idx;
        c.add_def(gvn.con(idx==-1 ? TypeRPC.ALL_CALL : fun._tf._ts._ts[idx])); // Generic arg#1
        for( int j=2; j<_defs._len; j++ ) // Get the new parm path or null according to split
          c.add_def( fun.at(j)==any ? any : n.at(j) );
      } else if( n != this ) {  // Interior nodes
        for( Node def : n._defs ) {
          Node newdef = map.get(def);
          if( def==epi )  // If using the old epilog in a recursive fcn,
            newdef = new_unr; // need to point to the function-choice which includes the old fcn
          c.add_def(newdef==null ? def : newdef);
        }
      }
    }
    // Kill split-out path-ins to the old code
    for( int j=2; j<_defs._len; j++ )
      if( fun.at(j)!=any )  // Path split out?
        set_def(j,any,gvn); // Kill incoming path on old FunNode

    // The old Epilog has sets of result Casts and RPCs; these need to be
    // split and half repointed to the new Epilog.  RPCs first.
    for( int j=0; !epi.is_dead() && j<epi._uses._len; j++ ) {
      Node use = epi._uses.at(j);
      if( !(use instanceof RPCNode) ) continue;
      int i, rpc_idx = ((RPCNode)use)._rpc;
      for( i=2; i<_defs._len; i++ )
        if( rpc_idx == ((TypeRPC)gvn.type(rpc_parm.at(i))).rpc() )
          break;
      assert i<_defs._len;      // Must find each RPC associated path
      if( fun.at(i)!=any ) {
        gvn.set_def_reg(use,0,newepi);
        gvn.set_def_reg(use,1,newepi);
        j--;            // Rerun loop since changed the set being iterated over
      }
    }
    // Now repoint any Casts
    for( int j=0; !epi.is_dead() && j<epi._uses._len; j++ ) {
      Node use = epi._uses.at(j);
      if( !(use instanceof CastNode) ) continue;
      if( use.at(0) instanceof RPCNode && use.at(0).at(0)==newepi ) {
        assert use.at(1)==epi;
        gvn.set_def_reg(use,1,newepi);
        j--;
      }
    }
    // Repoint all other uses to an Unresolved choice of the old and new functions
    if( fun.at(1) != any ) gvn.subsume(epi,new_unr);
    
    // Put all new nodes into the GVN tables and worklists
    for( Node c : map.values() ) gvn.rereg(c);
    // TODO: Hook with proper signature into ScopeNode under an Unresolved.
    // Future calls may resolve to either the old version or the new.
    return is_dead() ? fun : this;
  }

  @Override public Type value(GVNGCM gvn) {
    return _tf.is_forward_ref() || !callers_known(gvn) ? Type.CTRL : super.value(gvn);
  }
  
  @Override public int hashCode() { return super.hashCode()+_tf.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FunNode) ) return false;
    FunNode fun = (FunNode)o;
    return _tf==fun._tf;
  }
  @Override public byte op_prec() { return _op_prec; }
}
