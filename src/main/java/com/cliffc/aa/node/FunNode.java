package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;

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
public class FunNode extends RegionNode {
  private static int CNT=1; // Function index; -1 for 'all' and 0 for 'any'
  public TypeFun _tf;       // Worse-case correct type, updated by GCP
  private final byte _op_prec;// Operator precedence; only set top-level primitive wrappers

  // FunNodes can "discover" callers if the function constant exists in the
  // program anywhere (since, during execution (or optimizations) it may arrive
  // at a CallNode and initiate a new call to the function).  Until all callers
  // are accounted for, the FunNode keeps slot1 reserved with the most
  // conservative allowed arguments, under the assumption a as-yet-detected
  // caller will call with such arguments.  This is a quick check to detect
  // may-have-more-callers.
  public boolean _all_callers_known = false;
  
  // Used to make the primitives at boot time
  public FunNode(Node scope, PrimNode prim) { this(scope,TypeFun.make(prim._targs,prim._ret,CNT,prim._targs._ts.length),prim.op_prec(),prim._name); }
  // Used to make copies when inlining/cloning function bodies
  private FunNode(Node scope, TypeTuple ts, Type ret, String name, int nargs) { this(scope,TypeFun.make(ts,ret,CNT,nargs),-1,name); }
  // Used to start an anonymous function in the Parser
  public FunNode(int nargs, Node scope) { this(scope,TypeFun.any(nargs,CNT),-1,null); }
  // Used to forward-decl anon functions
  FunNode(Node scope, String name) { this(scope,TypeFun.make_forward_ref(CNT),-1,name); }
  // Shared common constructor
  private FunNode(Node scope, TypeFun tf, int op_prec, String name) {
    super(OP_FUN);
    if( scope != null ) add_def(scope);
    _tf = tf;
    _op_prec = (byte)op_prec;
    if( name != null ) bind(name);
    FUNS.add(this);             // Track FunNode by fidx
    CNT++;                      // Bump global unique fidx number
  }
  
  // Fast reset of parser state between calls to Exec
  static int PRIM_CNT;
  public static void init0() { PRIM_CNT=CNT; }
  public static void reset_to_init0() { CNT = PRIM_CNT; NAMES.set_len(PRIM_CNT); FUNS.set_len(PRIM_CNT); }

  // Find FunNodes by fidx
  private static Ary<FunNode> FUNS = new Ary<>(new FunNode[]{null,});
  public static FunNode find_fidx(int fidx) { return FUNS.at(fidx); }

  @Override String xstr() { return _tf.toString(); }
  @Override String str() { return names(_tf._fidxs,new SB()).toString(); }
  // Debug only: make an attempt to bind name to a function
  private static Ary<String> NAMES = new Ary<>(new String[1],0);
  public void bind( String tok ) {
    int fidx = _tf.fidx();
    String name = NAMES.atX(fidx);
    assert name==null || name.equals(tok); // Attempt to double-bind
    NAMES.setX(fidx,tok);
  }
  // Can return nothing, or "name" or "{name0,name1,name2...}"
  public static SB names(Bits fidxs, SB sb ) {
    int fidx = fidxs.abit();
    if( fidx >= 0 ) return name(fidx,sb);
    sb.p('{');
    int cnt=0;
    for( Integer ii : fidxs ) {
      if( ++cnt==4 ) break;
      name(ii,sb).p(fidxs.above_center()?'+':',');
    }
    if( cnt>=4 || fidxs.inf() ) sb.p("...");
    sb.p('}');
    return sb;
  }
  private static SB name( int i, SB sb ) {
    String name = NAMES.atX(i);
    return sb.p(name==null ? Integer.toString(i) : name);
  }
  public String name() { return name(_tf.fidx()); }
  public static String name(int fidx) { return NAMES.atX(fidx); }

  @Override Node copy() {
    throw AA.unimpl();          // Gotta make a new FIDX
  }

  // Declare as all-callers-known.  Done by GCP after flowing function-pointers
  // to all call sites, and by inlining when making private copies.
  public void all_callers_known( ) {
    assert !_all_callers_known;
    _all_callers_known = true;
  }
  
  // ----
  @Override public Node ideal(GVNGCM gvn) {
    // Generic Region ideal
    Node n = ideal(gvn,!_all_callers_known);
    if( n!=null ) return n;

    if( gvn._small_work ) { // Only doing small-work now
      gvn.add_work2(this);  // Maybe want to inline later
      return null;
    }
      
    // Type-specialize as-needed
    if( _tf.is_forward_ref() ) return null;
    ParmNode[] parms = new ParmNode[_tf.nargs()];
    EpilogNode epi = split_callers_gather(gvn,parms);
    if( epi == null ) return null;
    // Look for appropriate type-specialize callers
    FunNode fun = type_special(gvn,parms);
    if( fun == null ) { // No type-specialization to do
      // Large code-expansion allowed; can inline for other reasons
      fun = split_size(gvn,epi,parms);
      if( fun == null ) return null;
    }
    // Split the callers according to the new 'fun'.
    return split_callers(gvn,rpc(),epi,fun);
  }

  private EpilogNode split_callers_gather( GVNGCM gvn, ParmNode[] parms ) {
    for( int i=1; i<_defs._len; i++ ) if( gvn.type(in(i))==Type.XCTRL ) return null;
    if( _defs._len <= 2 ) return null; // No need to split callers if only 1

    // Gather the ParmNodes and the EpilogNode.  Ignore other (control) uses
    EpilogNode epi = null;
    for( Node use : _uses )
      if( use instanceof ParmNode ) {
        ParmNode parm = (ParmNode)use;
        assert !(gvn.type(use) instanceof TypeErr);
        //Type pt = gvn.type(parm);
        //if( pt instanceof TypeErr && !pt.above_center() && pt != TypeErr.ALL ) return null;
        if( parm._idx != -1 ) parms[parm._idx] = parm;
      } else if( use instanceof EpilogNode ) { assert epi==null || epi==use; epi = (EpilogNode)use; }
    return epi;                 // Epilog (or null if dead)
  }


  // Visit all ParmNodes, looking for unresolved call uses that can be improved
  // by type-splitting
  private int find_type_split_index( GVNGCM gvn, ParmNode[] parms ) {
    for( ParmNode parm : parms )// For all parms
      if( parm != null )        //   (some can be dead)
        for( Node call : parm._uses ) // See if a parm-user needs a type-specialization split
          if( call instanceof CallNode &&
              call.in(1) instanceof UnresolvedNode ) { // Call overload not resolved
            Type t0 = gvn.type(parm.in(1));            // Generic type in slot#1
            for( int i=2; i<parm._defs._len; i++ ) {   // For all other inputs
              Type ti = gvn.type(parm.in(i)).widen();  // Get the widen'd type
              assert ti.isa(t0);                       // Must be isa-generic type, or else type-error
              if( ti != t0 ) return i; // Sharpens?  Then splitting here should help
            }
            // Else no split will help this call, look for other calls to help
          }
    return -1; // No unresolved calls; no point in type-specialization
  }

  // Look for type-specialization inlining.  If any ParmNode has an unresolved
  // Call user, then we'd like to make a clone of the function body (in least
  // up to getting all the function TypeUnions to clear out).  The specialized
  // code uses generalized versions of the arguments, where we only specialize
  // on arguments that help immediately.
  private FunNode type_special( GVNGCM gvn, ParmNode[] parms ) {
    int idx = find_type_split_index(gvn,parms);
    if( idx == -1 ) return null; // No unresolved calls; no point in type-specialization

    // If Parm has unresolved calls, we want to type-specialize on its
    // arguments.  Call-site #1 is the most generic call site for the parser
    // (all Scalar args).  Peel out 2nd call-site args and generalize them.
    Type[] sig = new Type[parms.length];
    for( int i=0; i<parms.length; i++ )
      sig[i] = parms[i]==null ? Type.SCALAR : gvn.type(parms[i].in(idx)).widen();
    // Make a new function header with new signature
    TypeTuple ts = TypeTuple.make_args(sig);
    assert ts.isa(_tf._ts);
    assert ts != _tf._ts;            // Must see improvement
    // Make a prototype new function header.  Clone the generic unknown caller in slot 1.  
    assert !_all_callers_known;
    FunNode fun = new FunNode(in(1),ts,_tf._ret,name(),_tf._nargs);
    // Look in remaining paths and decide if they split or stay
    Node xctrl = gvn.con(Type.XCTRL);
    for( int j=2; j<_defs._len; j++ ) {
      boolean split=true;
      for( int i=0; i<parms.length; i++ )
        split &= parms[i] == null || gvn.type(parms[i].in(j)).widen().isa(sig[i]);
      fun.add_def(split ? in(j) : xctrl);
    }
    // TODO: Install in ScopeNode for future finding
    fun._all_callers_known = false;
    return fun;
  }

  // Split a single-use copy (e.g. fully inline) if the function is "small
  // enough".  Include anything with just a handful of primitives, or a single
  // call, possible with a single if.
  private FunNode split_size( GVNGCM gvn, EpilogNode epi, ParmNode[] parms ) {
    int[] cnts = new int[OP_MAX];
    BitSet bs = new BitSet();
    Ary<Node> work = new Ary<>(new Node[1],0);
    work.add(this);             // Prime worklist
    while( work._len > 0 ) {    // While have work
      Node n = work.pop();      // Get work
      if( bs.get(n._uid) ) continue; // Already visited?
      bs.set(n._uid);           // Flag as visited
      int op = n._op;           // opcode
      if( op == OP_FUN  && n       != this ) continue; // Call to other function, not part of inlining
      if( op == OP_PARM && n.in(0) != this ) continue; // Arg  to other function, not part of inlining
      if( n != epi )            // Except for the Epilog
        work.addAll(n._uses);   // Visit all uses also
      if( op==OP_CALL ) {       // Call-of-primitive?
        Node n1 = n.in(1);
        Node n2 = n1 instanceof UnresolvedNode ? n1.in(0) : n1;
        if( n2 instanceof EpilogNode &&
            ((EpilogNode)n2).val() instanceof PrimNode )
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

    // Pick which input to inline.  Only based on having some constant inputs
    // right now.
    int m=-1, mncons = -1;
    for( int i=2; i<_defs._len; i++ ) {
      int ncon=0;
      for( ParmNode parm : parms ) {
        if( parm != null &&
            gvn.type(parm.in(i)).is_con() )
          ncon++;
      }
      if( ncon > mncons ) { mncons = ncon; m = i; }
    }

    
    // Make a prototype new function header.  No generic unknown caller
    // in slot 1.  The one inlined call in slot 'm'.
    Node top = gvn.con(Type.XCTRL);
    FunNode fun = new FunNode(top,_tf._ts,_tf._ret,name(),_tf._nargs);
    for( int i=2; i<_defs._len; i++ )
      fun.add_def(i==m ? in(i) : top);
    fun.all_callers_known();    // Only 1 caller
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
      int op = n._op;           // opcode
      if( op == OP_FUN  && n       != this ) continue; // Call to other function, not part of inlining
      if( op == OP_PARM && n.in(0) != this ) continue; // Arg  to other function, not part of inlining
      assert n._uid < fun._uid; // Recursive calls will call 'fun' directly
      assert n.in(0)!=epi && (n._defs._len<=1 || n.in(1)!= epi || n instanceof CallNode); // Do not walk past epilog
      if( n != epi )           // Except for the Epilog
        work.addAll(n._uses);  // Visit all uses also
      map.put(n,n.copy()); // Make a blank copy with no edges and map from old to new
    }
    // Correct new function index
    EpilogNode newepi = (EpilogNode)map.get(epi);
    newepi._fidx = fun._tf.fidx();

    // Fill in edges.  New Nodes point to New instead of Old; everybody
    // shares old nodes not in the function (and not cloned).  The
    // FunNode & Parms only get the matching slice of args.
    Node  any = gvn.con(Type.XCTRL);
    Node dany = gvn.con(Type.XSCALAR);
    for( Node n : map.keySet() ) {
      Node c = map.get(n);
      if( n instanceof ParmNode && n.in(0) == this ) {  // Leading edge ParmNodes
        c.add_def(map.get(n.in(0))); // Control
        // Slot#1 for a type-split gets the new generic type from the new signature.
        // Slot#1 for other live splits gets from the old parm inputs.
        int idx = ((ParmNode)n)._idx;
        c.add_def(gvn.con(idx==-1 ? TypeRPC.ALL_CALL : fun._tf.arg(idx))); // Generic arg#1
        for( int j=2; j<_defs._len; j++ ) // Get the new parm path or null according to split
          c.add_def( fun.in(j)==any ? dany : n.in(j) );
      } else if( n != this ) {  // Interior nodes
        for( Node def : n._defs ) {
          // Map old to new, except if using the old epilog in a recursive fcn,
          // need to stay pointing to the old fcn.  The epilog choices will be
          // updated further below.
          Node newdef = def==epi ? def : map.get(def);
          c.add_def(newdef==null ? def : newdef);
        }
      }
    }

    // Kill split-out path-ins to the old code.  If !_all_callers_known then
    // always keep slot#1, otherwise kill slots being taken over by the new
    // function.
    for( int j=_all_callers_known ? 1 : 2; j<_defs._len; j++ )
      if( fun.in(j)!=any )  // Path split out?
        set_def(j,any,gvn); // Kill incoming path on old FunNode

    // Put all new nodes into the GVN tables and worklists
    for( Map.Entry<Node,Node> e : map.entrySet() ) {
      Node nn = e.getValue();         // New node
      Type ot = gvn.type(e.getKey()); // Generally just copy type from original nodes
      if( nn instanceof ParmNode && ((ParmNode)nn)._idx==-1 )
        ot = nn.all_type();     // Except the RPC, which has new callers
      else if( nn instanceof EpilogNode ) {
        TypeTuple tt = (TypeTuple)ot; // And the epilog, which has a new funnode and RPCs
        ot = TypeTuple.make_all(tt.at(0),tt.at(1),TypeRPC.ALL_CALL,fun._tf);
      }
      gvn.rereg(nn,ot);
    }
    assert !epi.is_dead();      // Not expecting this to be dead already

    // Repoint all Calls uses to an Unresolved choice of the old and new
    // functions and let the Calls resolve individually.
    if( !fun._all_callers_known ) { // Split-for-type, possible many future callers
      UnresolvedNode new_unr = new UnresolvedNode();
      new_unr.add_def(epi);
      gvn.init(new_unr);

      // Direct all Call uses to the new Unresolved
      for( int i=0; i<epi._uses._len; i++ ) {
        Node call = epi._uses.at(i);
        if( call instanceof CallNode && call.in(1)==epi ) {
          gvn.set_def_reg(call,1,new_unr);// As part of removing call->epi edge, compress epi uses
          i--;             // Rerun set point in epi use list after compression
        }
      }
      // Include the new Epilog in all Unresolved
      for( int i=0; i<epi._uses._len; i++ ) {
        Node unr = epi._uses.at(i);
        assert !(unr instanceof CallNode);
        if( unr instanceof UnresolvedNode )
          gvn.add_def(unr,newepi);
      }      

    } else {                    // All-callers-known, so actually only 1
      // Single path being inlined
      int path_being_inlined=-1;
      for( int j=1; j<_defs._len; j++ )
        if( fun.in(j)!=any )
          path_being_inlined = j;

      // The old Epilog has a set of CallNodes, but only the one in #path_being_inlined is
      // being split-for-size.  Repoint the one Call._rpc matching rpc_parm
      // in(path_being_inlined) to new_epi.
      int rpc = ((TypeRPC)gvn.type(rpc_parm.in(path_being_inlined))).rpc();
      for( Node use : epi._uses ) {
        if( use instanceof CallNode && 
            ((CallNode)use)._rpc == rpc ) {
          gvn.set_def_reg(use,1,newepi);
          break;
        }
      }
    }

    // TODO: Hook with proper signature into ScopeNode under an Unresolved.
    // Future calls may resolve to either the old version or the new.
    return is_dead() ? fun : this;
  }

  // TODO: During GCP, slot#1 is the "default" input and assumed never
  // called.  As callers appear, they wire up and become actual input edges.
  // Leaving slot#1 alive here makes every call appear to be called by the
  // default caller.  Fix is to have the default (undiscovered) caller
  // control be different from the top-level REPL caller, and set the
  // undiscovered control to XCTRL.
  boolean slot1(GVNGCM gvn) {
    if( _all_callers_known ) return true;
    if( !gvn._opt ) return true;
    // TODO: Also check to see if this is a function being returned as a
    // top-level result.  This is only a partial fix, and only to make the body
    // executable - in case the only use is to return from the parser.
    Node s = in(1);
    if( !(s instanceof ScopeNode) ) return false;
    if( s._defs._len < 3 ) return false;
    Node e = s.in(s._defs._len-2); // EPilog
    if( !(e instanceof EpilogNode) ) return false;
    if( ((EpilogNode)e).fun() != this ) return false;
    return true;
  }
  
  // Compute value from inputs.  Slot#1 is always the unknown caller.  If
  // Slot#1 is not a ScopeNode, then it is a constant CTRL just in case we make
  // a new caller (e.g. via inlining).  If there are no other inputs and no
  // data uses, then the function is dead.  If there are data uses, they might
  // hit a new CallNode - and this requires GCP to discover the full set of
  // possible callers.
  @Override public Type value(GVNGCM gvn) {
    // Will be an error eventually, but act like its executed so the trailing EpilogNode gets visited during GCP
    if( _tf.is_forward_ref() ) return Type.CTRL;
    // TODO: During GCP, slot#1 is the "default" input and assumed never
    // called.  As callers appear, they wire up and become actual input edges.
    // Leaving slot#1 alive here makes every call appear to be called by the
    // default caller.  Fix is to have the default (undiscovered) caller
    // control be different from the top-level REPL caller, and set the
    // undiscovered control to XCTRL.
    int s = slot1(gvn) ? 1 : 2;
    Type t = Type.XCTRL;
    for( int i=s; i<_defs._len; i++ )
      t = t.meet(gvn.type(in(i)));
    return t;
  }

  public ParmNode rpc() {
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx==-1 )
        return (ParmNode)use;
    return null;
  }
  public EpilogNode epi() {
    for( Node use : _uses )
      if( use instanceof EpilogNode )
        return (EpilogNode)use;
    return null;
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
