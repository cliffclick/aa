package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
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
// FunNodes are finite in count and are unique densely numbered, see BitsFun.
//
// Pointing to the FunNode are ParmNodes which are also PhiNodes; one input
// path for each known caller.  Zero slot points to the FunNode.  Arg1 points
// to the generic unknown worse-case caller (a type-specific ConNode with
// worse-case legit bottom type).  The collection of these ConNodes can share
// TypeVars to structurally type the inputs.  ParmNodes merge all input path
// types (since they are a Phi), and the call "loses precision" for type
// inference there.  Parm#0 (NOT the zero-slot but the zero idx) is the
// incoming memory argument.  Parm#1 and up (NOT the one-slot but the one idx)
// are the classic function arguments.
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
  public TypeFunPtr _tf;        // Worse-case correct type, updated by GCP
  private final byte _op_prec;  // Operator precedence; only set top-level primitive wrappers
  
  // Used to make the primitives at boot time
  public FunNode(PrimNode prim, Type ret, TypeMem retmem) {
    this(TypeFunPtr.make_new(prim._targs,ret,retmem,BitsFun.ALL,prim._targs._ts.length),prim.op_prec(),prim._name); }
  // Used to make copies when inlining/cloning function bodies
  private FunNode(TypeTuple ts, Type ret, TypeMem retmem, int parent_fidx, String name, int nargs) {
    this(TypeFunPtr.make_new(ts,ret,retmem,parent_fidx, nargs),-1,name); }
  // Used to start an anonymous function in the Parser, includes argument memory in ts[0]
  public FunNode(Type[] ts) { this(TypeFunPtr.make_new(TypeTuple.make(ts),Type.SCALAR,TypeMem.MEM,BitsFun.ALL,ts.length),-1,null); }
  // Used to forward-decl anon functions
  FunNode(String name) { this(TypeFunPtr.make_forward_ref(),-1,name); }
  // Shared common constructor
  private FunNode(TypeFunPtr tf, int op_prec, String name) {
    super(OP_FUN);
    add_def(Env.ALL_CTRL);
    _tf = tf;
    _op_prec = (byte)op_prec;
    if( name != null ) bind(name);
    FUNS.setX(tf.fidx(),this); // Track FunNode by fidx
  }
  
  // Fast reset of parser state between calls to Exec
  public static void init0() { }
  public static void reset_to_init0() { NAMES.set_len(BitsFun.PRIM_CNT); FUNS.set_len(BitsFun.PRIM_CNT); }

  // Find FunNodes by fidx
  static Ary<FunNode> FUNS = new Ary<>(new FunNode[]{null,});
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
  public static SB names(BitsFun fidxs, SB sb ) {
    int fidx = fidxs.abit();
    if( fidx >= 0 ) return name(fidx,sb);
    sb.p('{');
    int cnt=0;
    for( Integer ii : fidxs ) {
      if( ++cnt==4 ) break;
      name(ii,sb).p(fidxs.above_center()?'+':',');
    }
    if( cnt>=4 ) sb.p("...");
    sb.p('}');
    return sb;
  }
  private static SB name( int i, SB sb ) {
    String name = NAMES.atX(i);
    return sb.p(name==null ? Integer.toString(i) : name);
  }
  public String name() { return name(_tf.fidx()); }
  public static String name(int fidx) { return NAMES.atX(fidx); }

  @Override Node copy(GVNGCM gvn) { throw AA.unimpl(); } // Gotta make a new FIDX

  // True if no future unknown callers.
  private boolean has_unknown_callers() { return in(1) == Env.ALL_CTRL; }

  Type targ(int idx) {
    return idx == -1 ? TypeRPC.ALL_CALL : _tf.arg(idx);
  }
  
  // ----
  @Override public Node ideal(GVNGCM gvn) {
    // Generic Region ideal
    Node n = super.ideal(gvn);
    if( n!=null ) return n;

    if( gvn._small_work ) { // Only doing small-work now
      gvn.add_work2(this);  // Maybe want to inline later
      return null;
    }
      
    // Type-specialize as-needed
    if( _tf.is_forward_ref() ) return null;
    ParmNode rpc_parm = rpc();
    if( rpc_parm == null ) return null; // Single caller const-folds the RPC, but also inlines in CallNode
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
    return split_callers(gvn,rpc_parm,epi,fun);
  }

  // Gather the ParmNodes into an array.  Return null if any input path is dead
  // (would rather fold away dead paths before inlining).  Return null if there
  // is only 1 path.  Return null if any actuals are not formals.
  private EpilogNode split_callers_gather( GVNGCM gvn, ParmNode[] parms ) {
    for( int i=1; i<_defs._len; i++ ) if( gvn.type(in(i))==Type.XCTRL ) return null;
    if( _defs._len <= 2 ) return null; // No need to split callers if only 1

    // Gather the ParmNodes and the EpilogNode.  Ignore other (control) uses
    EpilogNode epi = null;
    for( Node use : _uses )
      if( use instanceof ParmNode ) {
        ParmNode parm = (ParmNode)use;
        if( parm._idx != -1 ) {
          // Check that all actuals are isa all formals.  This is a little
          // conservative, as we could inline on non-error paths.
          for( int i=1; i<_defs._len; i++ )
            if( !gvn.type(parm.in(i)).isa(_tf.arg(parm._idx)) )
              return null; // Actual !isa formal; do not inline while in-error
          // TODO: FAILS for -2, memory arg.
          // TODO: Ponder swapping all parms+1 idx, and reversing memory_idx for 0
          parms[parm._idx] = parm;
        }
      } else if( use instanceof EpilogNode ) { assert epi==null || epi==use; epi = (EpilogNode)use; }
    return epi;                 // Epilog (or null if dead)
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
              Type ti = gvn.type(parm.in(i)).widen();  // Get the widen'd type
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
      // Memory is parm#0, and default memory allows all memory input state.
      // Also, widen() for memory currently does not do anything.
      sig[0] = parms[0]==null ? TypeMem.MEM : gvn.type(parms[0].in(idx)).widen();
      for( int i=1; i<parms.length; i++ )
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
  private FunNode type_special( GVNGCM gvn, ParmNode[] parms ) {
    if( !has_unknown_callers() ) return null; // Only overly-wide calls.
    Type[] sig = find_type_split(gvn,parms);
    if( sig == null ) return null; // No unresolved calls; no point in type-specialization

    // If Parm has unresolved calls, we want to type-specialize on its
    // arguments.  Call-site #1 is the most generic call site for the parser
    // (all Scalar args).  Peel out 2nd call-site args and generalize them.
    
    // Make a new function header with new signature
    TypeTuple ts = TypeTuple.make(sig);
    assert ts.isa(_tf._ts);
    assert ts != _tf._ts;            // Must see improvement
    // Make a prototype new function header.
    FunNode fun = new FunNode(ts,_tf._ret,_tf._retmem,_tf.fidx(),name(),_tf._nargs);
    // Look in remaining paths and decide if they split or stay
    Node xctrl = gvn.con(Type.XCTRL);
    for( int j=2; j<_defs._len; j++ ) {
      boolean split=true;
      for( int i=0; i<parms.length; i++ )
        split &= parms[i] == null || gvn.type(parms[i].in(j)).widen().isa(sig[i]);
      fun.add_def(split ? in(j) : xctrl);
    }
    return fun;
  }

  // Split a single-use copy (e.g. fully inline) if the function is "small
  // enough".  Include anything with just a handful of primitives, or a single
  // call, possible with a single if.
  private FunNode split_size( GVNGCM gvn, EpilogNode epi, ParmNode[] parms ) {
    if( _defs._len <= 1 ) return null; // No need to split callers if only 2
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
        Node n1 = ((CallNode)n).fun();
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

    // Pick which input to inline.  Only based on having some constant inputs
    // right now.
    int m=-1, mncons = -1;
    for( int i=has_unknown_callers() ? 2 : 1; i<_defs._len; i++ ) {
      int ncon=0;
      for( ParmNode parm : parms )
        if( parm != null &&     // Some can be dead
            gvn.type(parm.in(i)).is_con() )
          ncon++;
      if( ncon > mncons ) { mncons = ncon; m = i; }
    }

    // Specifically ignoring constants, parms, phis, rpcs, types,
    // unresolved, and casts.  These all track & control values, but actually
    // do not generate any code.
    if( cnts[OP_CALL] > 1 || // Careful inlining more calls; leads to exponential growth
        cnts[OP_IF  ] > 1+mncons || // Allow some trivial filtering to inline
        cnts[OP_PRIM] > 6 )  // Allow small-ish primitive counts to inline
      return null;

    // Make a prototype new function header.  No generic unknown caller
    // in slot 1.  The one inlined call in slot 'm'.
    // Make a prototype new function header.
    FunNode fun = new FunNode(_tf._ts,_tf._ret,_tf._retmem,_tf.fidx(),name(),_tf._nargs);
    fun.pop();                  // Remove junk ALL_CTRL input
    Node top = gvn.con(Type.XCTRL);
    for( int i=1; i<_defs._len; i++ )
      fun.add_def(i==m ? in(i) : top);
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
      map.put(n,n.copy(gvn));  // Make a blank copy with no edges and map from old to new
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
        Node x = has_unknown_callers() 
          // type-split; maybe more unknown callers... so slot#1 remains generic
          ? gvn.con(fun.targ(idx))             // Generic arg#1
          : (fun.in(1)==any ? dany : n.in(1)); // Just another argument
        c.add_def(x); 
        for( int j=2; j<_defs._len; j++ ) // Get the new parm path or null according to split
          c.add_def( fun.in(j)==any ? dany : n.in(j) );
        // Update default type to match signature
        if( idx != -1 && idx != -2 ) ((ParmNode)c)._default_type = fun._tf.arg(idx);
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
    if( dany._uses._len==0 ) gvn.kill(dany);
    // Kill split-out path-ins to the old code.  If !_all_callers_known then
    // always keep slot#1, otherwise kill slots being taken over by the new
    // function.
    for( int j=has_unknown_callers() ? 2 : 1; j<_defs._len; j++ )
      if( fun.in(j)!=any )  // Path split out?
        set_def(j,any,gvn); // Kill incoming path on old FunNode
    
    // Put all new nodes into the GVN tables and worklists
    for( Map.Entry<Node,Node> e : map.entrySet() ) {
      Node nn = e.getValue();         // New node
      Type ot = gvn.type(e.getKey()); // Generally just copy type from original nodes
      if( nn instanceof ParmNode && ((ParmNode)nn)._idx==-1 )
        ot = nn.all_type();     // Except the RPC, which has new callers
      else if( nn instanceof EpilogNode ) {
        TypeFun tt = (TypeFun)ot; // And the epilog, which has a new funnode and RPCs
        ot = TypeFun.make(tt.ctl(),tt.mem(),tt.val(),TypeRPC.ALL_CALL,fun._tf);
      }
      gvn.rereg(nn,ot);
    }
    assert !epi.is_dead();      // Not expecting this to be dead already
    
    // Repoint all Calls uses of the original Epilog to an Unresolved choice of
    // the old and new functions and let the Calls resolve individually.
    if( _tf._ts != fun._tf._ts ) { // Split-for-type, possible many future callers
      UnresolvedNode new_unr = new UnresolvedNode();
      new_unr.add_def(epi);
      gvn.init(new_unr);
    
      // Direct all Call uses to the new Unresolved
      for( int i=0; i<epi._uses._len; i++ ) {
        Node call = epi._uses.at(i);
        if( call instanceof CallNode && ((CallNode)call).fun()==epi ) {
          ((CallNode)call).set_fun_reg(new_unr,gvn);// As part of removing call->epi edge, compress epi uses
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
    
    } else {                    // Split-for-size and only 1 caller
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
          ((CallNode)use).set_fun_reg(newepi,gvn);
          break;
        }
      }
    }

    // There are new some cloned new Calls; these point to some old functions
    // which might believe "all_calls_known" - which excludes these new Calls.
    // The situation is still theoretically correct: the original Calls all
    // split into 2 non-overlapping sets: calls from the new Calls and those
    // left behind coming from the old Calls.  Update the old functions with
    // these new Calls as-needed.  If has_unknown_callers(), the old
    // function is prepared to handle unexpected new Calls already.  If its
    // not true, then immediately wire up the new Call, add the new RPC input and
    // correct all types.
    if( !is_dead() && !has_unknown_callers() )
      for( Node c : map.values() ) {
        if( c instanceof CallNode ) { // For all cloned Calls
          CallNode call = (CallNode)c;
          Type tfunptr = gvn.type(call.fun());
          TypeFunPtr tfun = ((TypeFun)tfunptr).fun();
          for( int fidx : tfun._fidxs ) { // For all possible targets of the Call
            FunNode oldfun = FunNode.find_fidx(fidx);
            assert !oldfun.is_dead();
            if( !oldfun.has_unknown_callers() ) {
              gvn.add_work(oldfun);
              Node x = ((CallNode)c).wire(gvn,oldfun,false);
              assert x != null;
              ParmNode rpc = oldfun.rpc();
              if( rpc != null ) // Can be null there is a single return point, which got constant-folded
                gvn.setype(rpc,rpc.value(gvn));
              EpilogNode oldepi = oldfun.epi();
              gvn.setype(oldepi,oldepi.value(gvn));
            }
          }
        }
      }

    // TODO: Hook with proper signature into ScopeNode under an Unresolved.
    // Future calls may resolve to either the old version or the new.
    return is_dead() ? fun : this;
  }

  // Compute value from inputs.  Simple meet over inputs.
  @Override public Type value(GVNGCM gvn) {
    // Will be an error eventually, but act like its executed so the trailing
    // EpilogNode gets visited during GCP
    if( _tf.is_forward_ref() ) return Type.CTRL;
    Type t = Type.XCTRL;
    for( int i=1; i<_defs._len; i++ )
      t = t.meet(gvn.type(in(i)));
    return t;
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _tf.is_forward_ref(); }
  ParmNode parm( int idx ) {
    for( Node use : _uses )
      if( use instanceof ParmNode && ((ParmNode)use)._idx==idx )
        return (ParmNode)use;
    return null;
  }
  public ParmNode rpc() { return parm(-1); }
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
