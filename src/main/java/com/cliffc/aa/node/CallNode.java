package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;

// Call/apply node.
//
// Control is not required for an apply but inlining the function body will
// require it; slot 0 is for Control.  Slot 1 is a function value - a Node
// typed as a TypeFunPtr; can be a FunPtrNode, an Unresolved, or e.g. a Phi or
// a Load.  Slot 2 is for memory.  Slots 3+ are for other args.
//
// When the function type simplifies to a single TypeFunPtr, the Call can inline.
//
// TFPs are actually Closures and include an extra argument for the enclosed
// environment (actually expanded out to one arg-per-used-scope).  These extra
// arguments are part of the function signature but are not direct inputs into
// the call.
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
public class CallNode extends Node {
  int _rpc;                 // Call-site return PC
  boolean _unpacked;        // Call site allows unpacking a tuple (once)
  boolean _is_copy;         // One-shot flag set when inlining an entire single-caller-single-called
  Parse  _badargs;          // Error for e.g. wrong arg counts or incompatible args
  public CallNode( boolean unpacked, Parse badargs, Node... defs ) {
    super(OP_CALL,defs);
    _rpc = BitsRPC.new_rpc(BitsRPC.ALL); // Unique call-site index
    _unpacked=unpacked;         // Arguments are typically packed into a tuple and need unpacking, but not always
    _badargs = badargs;
  }

  String xstr() { return ((is_dead() || is_copy()) ? "x" : "C")+"all#"+_rpc; } // Self short name
  String  str() { return xstr(); }       // Inline short name

  // Call arguments:
  // 0 - Control.  If XCTRL, call is not reached.
  // 1 - Memory.  This is memory into the call.  The following MProj is memory
  //     passed to the called function - which is generally trimmed to just
  //     what the function can use.  The unused memory bypasses to the CallEpi.
  // 2 - Function pointer, typed as a TypeFunPtr.  Might be a FunPtrNode, might
  //     be e.g. a Phi or a Load.  This is argument 0, both as the Closure AND
  //     as the Code pointer.
  // 3+  Other "normal" arguments.

  // Number of actual arguments, including the closure/code ptr.
  int nargs() { return _defs._len-2; }
  // Argument type
  Type targ( GVNGCM gvn, int x ) {
    Type t = gvn.type(arg(x));
    if( x>0 ) return t;         // Normal argument type
    if( !(t instanceof TypeFunPtr) ) return Type.SCALAR;
    return ((TypeFunPtr)t).display(); // Extract Display type from TFP
  }
  // Actual arguments.  Arg(0) is allowed and refers to the Display/TFP.
  Node arg( int x ) { assert x>=0; return _defs.at(x+2); }
  // Set an argument.  Use 'set_fun' to set the Display/Code.
  Node set_arg    (int idx, Node arg, GVNGCM gvn) { assert idx>0; return set_def(idx+2,arg,gvn); }
  void set_arg_reg(int idx, Node arg, GVNGCM gvn) { assert idx>0; gvn.set_def_reg(this,idx+2,arg); }
  // Find output Proj for an argument
  ProjNode proj(int x) {
    for( Node use : _uses )
      if( use instanceof ProjNode && ((ProjNode)use)._idx==x+2 )
        return (ProjNode)use;
    return null;
  }

          Node ctl() { return in(0); }
  public  Node mem() { return in(1); }
  public  Node fun() { return in(2); }
          Node set_fun    (Node fun, GVNGCM gvn) { return set_def(2,fun,gvn); }
  public  void set_fun_reg(Node fun, GVNGCM gvn) { gvn.set_def_reg(this,2,fun); }
  public BitsFun fidxs(GVNGCM gvn) {
    Type tf = gvn.type(fun());
    return tf instanceof TypeFunPtr ? ((TypeFunPtr)tf).fidxs() : null;
  }

  // Clones during inlining all become unique new call sites.  The original RPC
  // splits into 2, and the two new children RPCs replace it entirely.  The
  // original RPC may exist in the type system for a little while, until the
  // children propagate everywhere.
  @Override @NotNull CallNode copy( boolean copy_edges, CallEpiNode unused, GVNGCM gvn) {
    CallNode call = (CallNode)super.copy(copy_edges,unused,gvn);
    ConNode old_rpc = gvn.con(TypeRPC.make(_rpc));
    call._rpc = BitsRPC.new_rpc(_rpc); // Children RPC
    Type oldt = gvn.unreg(this);       // Changes hash, so must remove from hash table
    _rpc = BitsRPC.new_rpc(_rpc);      // New child RPC for 'this' as well.
    gvn.rereg(this,oldt);              // Back on list
    // Swap out the existing old rpc users for the new.
    // Might be no users of either.
    ConNode new_rpc = gvn.con(TypeRPC.make(_rpc));
    gvn.add_work(gvn.subsume(old_rpc,new_rpc));
    return call;
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If inlined, no further xforms.  The using Projs will fold up.
    if( is_copy() ) return null;
    // Dead, do nothing
    TypeTuple tcall = (TypeTuple)gvn.type(this);
    Type tctl = tcall.at(0);
    Type tfp  = tcall.at(2);
    if( tctl!=Type.CTRL ) {
      if( (ctl() instanceof ConNode) ) return null;
      return set_def(0,gvn.con(Type.XCTRL),gvn); // Do chop off control usage
    }

    // When do I do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) { // Not yet unpacked a tuple
      assert nargs()==2;        // The Display plus the arg tuple
      Node mem = mem();
      Node arg1 = arg(1);
      Type tadr = gvn.type(arg1);
      // Bypass a merge on the 2-arg input during unpacking
      if( tadr instanceof TypeMemPtr && mem instanceof MemMergeNode ) {
        int alias = ((TypeMemPtr)tadr)._aliases.abit();
        if( alias == -1 ) throw AA.unimpl(); // Handle multiple aliases, handle all/empty
        Node obj = ((MemMergeNode)mem).alias2node(alias);
        if( obj instanceof OProjNode && arg1 instanceof ProjNode && arg1.in(0) instanceof NewNode ) {
          NewNode nnn = (NewNode)arg1.in(0);
          remove(_defs._len-1,gvn); // Pop off the NewNode tuple
          int len = nnn._defs._len;
          for( int i=2; i<len; i++ ) // Push the args; unpacks the tuple
            add_def( nnn.in(i));
          _unpacked = true;     // Only do it once
          return this;
        }
      }
    }
    // Have some sane function choices?
    if( !(tfp instanceof TypeFunPtr) ) return null;
    BitsFun fidxs = ((TypeFunPtr)tfp).fidxs();
    if( fidxs==BitsFun.EMPTY ) // TODO: zap function to empty function constant
      return null;             // Zero choices

    // If we have a single function allowed, force the function constant.
    Node unk = fun();           // Function epilog/function pointer
    int fidx = fidxs.abit();    // Check for single target
    if( fidx != -1 && !(unk instanceof FunPtrNode) )
      return set_fun(FunNode.find_fidx(fidx).ret().funptr(),gvn);

    // If the function is unresolved, see if we can resolve it now
    if( unk instanceof UnresolvedNode && // Unresolved
        !fidxs.above_center() ) {        // Only high if not executable/dying
      FunPtrNode fptr = least_cost(gvn, fidxs.dual()); // Check for least-cost target
      if( fptr != null ) return set_fun(fptr, gvn); // Resolve to 1 choice
    }

    // Wire targets that are not choices (1 or multi) with matching nargs even
    // with bad/low args; they may lift to good.  CallEpi will inline wired functions with good args.
    if( check_wire(gvn,fidxs) )
      return this;              // Some wiring happened

    // Check for dead args and trim; must be after all wiring is done because unknown
    // call targets can appear during GCP and use the args.
    if( gvn._opt_mode > 2 && err(gvn)==null ) {
      Node progress = null;
      for( int i=1; i<nargs(); i++ ) // Skip the FP/DISPLAY arg, as its useful for error messages
        if( ProjNode.proj(this,i)==null && !(arg(i) instanceof ConNode && targ(gvn,i)==Type.XSCALAR) )
          progress = set_arg(i,gvn.con(Type.XSCALAR),gvn); // Kill dead arg
      if( progress != null ) return this;
    }

    return null;
  }

  // Pass thru all inputs directly - just a direct gather/scatter.  The gather
  // enforces SESE which in turn allows more precise memory and aliasing.  The
  // full scatter lets users decide the meaning; e.g. wired FunNodes will take
  // the full arg set but if the call is not reachable the FunNode will not
  // merge from that path.  Result tuple type:
  @Override public TypeTuple value(GVNGCM gvn) {
    final Type[] ts = TypeAry.get(_defs._len);

    // Pinch to XCTRL/CTRL
    Type ctl = gvn.type(ctl());
    if( ctl == Type.ALL  ) ctl = Type. CTRL;
    if( ctl != Type.CTRL ) ctl = Type.XCTRL;
    if( !_is_copy && gvn._opt_mode>0 && cepi()==null ) ctl = Type.XCTRL; // Dead from below
    ts[0] = ctl;

    // Not a memory to the call?
    Type mem = gvn.type(mem());
    if( !(mem instanceof TypeMem) )
      mem = mem.above_center() ? TypeMem.EMPTY : TypeMem.FULL;
    ts[1] = mem;

    // If not called, then no memory to functions
    if( ctl == Type.XCTRL ) { ts[1] = TypeMem.EMPTY; }

    // Copy args for called functions.
    // If call is dead, then so are args.
    for( int i=0; i<nargs(); i++ )
      ts[i+2] = ctl==Type.XCTRL ? Type.XSCALAR : targ(gvn,i);

    // Not a function to call?
    Type tfx = gvn.type(fun());
    if( !(tfx instanceof TypeFunPtr) )
      tfx = tfx.above_center() ? TypeFunPtr.GENERIC_FUNPTR.dual() : TypeFunPtr.GENERIC_FUNPTR;
    TypeFunPtr tfp = (TypeFunPtr)(ts[2] = tfx);
    BitsFun fidxs = tfp.fidxs();
    // Specifically unwind Unresolved reporting low in ITER, and that low
    // report is so if we inline, Unresolved remains monotonic (it will lose
    // one of the inline requires vs losing an inline choice).  This means if
    // get some unresolved fptrs via some complex path we'll have to wait until
    // GCP to start resolving.
    BitsFun fidxs2 = fun() instanceof UnresolvedNode && gvn._opt_mode<2 ? fidxs.dual() : fidxs;
    // Resolve; keep choices with sane arguments.  If Resolve returns high,
    // then we have real choices and JOIN them.  If Resolve returns low, then
    // we have to handle all of them and we MEET them.
    BitsFun rfidxs = resolve(gvn,fidxs2,ts);
    if( !rfidxs.test(1) ) // Neither ANY nor ALL
      tfp = TypeFunPtr.make(rfidxs,tfp._args,tfp._ret);
    ts[2] = tfp;

    return TypeTuple.make(ts);
  }

  // Compute live across uses.  If pre-GCP, then we may not be wired and thus
  // have not seen all possible function-body uses.  Check for #FIDXs == nwired().
  @Override public TypeMem live( GVNGCM gvn) {
    if( gvn._opt_mode < 2 ) {
      BitsFun fidxs = fidxs(gvn);
      if( fidxs == null ) return TypeMem.FULL; // Assume Something Good will yet happen
      if( fidxs.above_center() ) return TypeMem.FULL; // Got choices, dunno which one will stick
      CallEpiNode cepi = cepi();
      if( cepi==null ) return _live; // Collapsing
      if( gvn.type(ctl()) == Type.XCTRL ) return _live; // Unreachable
      // Expand (actually fail) if any parents
      BitSet bs = fidxs.tree().plus_kids(fidxs);
      if( bs.cardinality() > cepi.nwired() ) // More things to call
        return TypeMem.FULL; // Cannot improve
    }
    // All choices discovered during GCP.  If the call is in-error it may not
    // resolve and so will have no uses other than the CallEpi - which is good
    // enough to declare this live, so it exists for errors.
    return super.live(gvn);
  }
  @Override public boolean basic_liveness() { return false; }


  // Resolve an Unresolved, Optimistically during GCP.  Called in value() and
  // so must be monotonic.  Strictly looks at arguments, and the list of
  // functions.
  //
  // GCP: fidx choices are above-center and get removed as args fall.  Resolve
  // keeps all fidx choices where the arguments are too-high (might fall to Ok)
  // or Ok: "actual.isa(formal)".  While there are choices, value() call uses
  // XCTRL instead of CTRL, to not enable functions which ultimately do not get
  // called.  At one choice, CTRL is on.  To maintain monotonicity this implies
  // that if there are ZERO choices (at least 1 arg is sideways or low for
  // every fidx) CTRL is ON, and bad args get passed to the ParmNodes.
  //
  // After args have fallen as far as they can, if we still have choices in GCP
  // we now pick based on the cost model (adding "nearly free" casts from e.g.
  // int->flt) to resolve.  This removes a choice, and we start falling again.
  //
  // After GCP, choices get locked in: Calls with a single fidx in their Type
  // upgrade their function input to the function constant.
  //
  // ITER: fidx choices are below-center, and get removed as args lift.
  // Resolve keeps all fidx choices where the arguments are too-low (might lift
  // to Ok) or Ok: "formal.dual().isa(actual)".  Where there are choices,
  // value() call uses CTRL - one or more of these choices WILL get called.
  // Only when the choice count drops to zero is CTRL turned off.
  //
  // If we run out of arg-too-low choices, and only have OK-args choices do we
  // use the cost model to pick amongst choices.  Choices with high-typed args
  // are always cheaper (int beats Scalar), so if the args later lift about the
  // choice's formals the other choices are also in-error.
  //
  // Given: BitsFun of choices, GVN _opt_mode and argument types.
  // Returns: set of choices where args match formals, and a flag is any are not OK.
  BitsFun resolve(GVNGCM gvn, BitsFun fidxs, Type[] targs) {
    if( fidxs==BitsFun.ANY ) return fidxs; // No point in attempting to resolve all things
    if( fidxs==BitsFun.FULL) return fidxs; // No point in attempting to resolve all things

    int hi = 1;
    BitsFun choices = BitsFun.EMPTY;
    for( int fidx : fidxs ) {
      int cmp = resolve(gvn,fidx,targs);
      // If any args are side, this is neither valid nor a choice.
      if( cmp==0 ) continue;
      // If any arg is eqv/good/low, this is a valid fun.
      // If all args are high, this is a choice fun.
      choices = choices.set(fidx);
      hi |= cmp;     // -1 (low) sticks; any low choice and all choices are low
    }
    return hi==1 ? choices.dual() : choices;
  }

  // Return 0 for not-a-choice, +1 for high choice, -1 for low choice.
  int resolve( GVNGCM gvn, int fidx, Type[] targs ) {
    if( BitsFun.is_parent(fidx) ) // Parent is never a real choice.  See these during inlining.
      throw com.cliffc.aa.AA.unimpl();

    FunNode fun = FunNode.find_fidx(fidx);
    if( fun==null || fun.is_dead() ) return 0; // Stale fidx leading to dead fun
    // Forward refs are only during parsing; assume they fit the bill
    if( fun.is_forward_ref() ) return 1;   // High choice
    if( fun.nargs() != nargs() ) return 0; // Wrong arg count, toss out
    if( fun.ret() == null ) throw com.cliffc.aa.AA.unimpl();
    TypeStruct formals = fun._tf._args; // Type of each argument
    //int low=0, good=0, high=0, side=0, eqv=0;
    boolean low_good=false,high=false;
    for( int j=0; j<fun.nargs(); j++ ) {
      Type actual = targs[j+2];
      if( j==0 && actual instanceof TypeFunPtr )
        actual = ((TypeFunPtr)actual).display(); // Extract Display type from TFP
      Type formal = formals.at(j);
      // actual is below a formal, above a formal, above a formal-dual, or
      // besides a formal.
      //if( actual==formal ) eqv++; // Arg is fine.  Covers NO_DISP which can be a high formal.
      //else if( formal.isa(actual) ) low++;
      //else if( formal.dual().meet(actual) ) good++;
      //else if( actual.meet(formal.dual()) ) high++;
      //else return 0;            // Side-ways not allowed

      if( actual==formal ) continue; // Arg is fine.  Covers NO_DISP which can be a high formal.
      Type mt = actual.meet(formal.dual());
      if( formal.isa(actual) || mt==actual ) low_good=true; // Low or Good
      else if( mt==formal.dual() ) high=true;
      else return 0;            // Side-ways not allowed
    }

    // If any arg is low/good, this is a low choice.
    // If all args are high, this is a high choice.
    return low_good || !high ? -1 : 1;
  }


  // Amongst these choices return the least-cost.  Some or all might be
  // invalid.
  public FunPtrNode least_cost(GVNGCM gvn, BitsFun choices) {
    assert choices.above_center(); // Must be some choices
    assert choices.bitCount() > 0; // Must be some choices
    int best_cvts=99999;           // Too expensive
    FunPtrNode best_fptr=null;     //
    TypeStruct best_formals=null;  //
    boolean tied=false;            // Ties not allowed
    for( int fidx : choices ) {
      if( BitsFun.is_parent(fidx) ) throw com.cliffc.aa.AA.unimpl();

      FunNode fun = FunNode.find_fidx(fidx);
      assert fun.nargs()==nargs() && fun.ret() != null;
      TypeStruct formals = fun._tf._args; // Type of each argument
      int cvts=0;                         // Arg conversion cost
      for( int j=0; j<fun.nargs(); j++ ) {
        Type actual = targ(gvn,j);
        Type formal = formals.at(j);
        if( actual==formal ) continue;
        byte cvt = actual.isBitShape(formal); // +1 needs convert, 0 no-cost convert, -1 unknown, 99 never
        if( cvt == -1 ) return null; // Might be the best choice, or only choice, dunno
        cvts += cvt;
      }

      if( cvts < best_cvts ) {
        best_cvts = cvts;
        best_fptr = fun.ret().funptr();
        best_formals = formals;
        tied=false;
      } else if( cvts==best_cvts ) {
        // Look for monotonic formals
        int fcnt=0, bcnt=0;
        for( int i=1; i<formals._ts.length; i++ ) {
          Type ff = formals.at(i), bf = best_formals.at(i);
          if( ff==bf ) continue;
          Type mt = ff.meet(bf);
          if( ff==mt ) bcnt++;       // Best formal is higher than new
          else if( bf==mt ) fcnt++;  // New  formal is higher than best
          else { fcnt=bcnt=-1; break; } // Not monotonic, no obvious winner
        }
        // If one is monotonically higher than the other, take it
        if( fcnt > 0 && bcnt==0 ) { best_fptr = fun.ret().funptr(); best_formals = formals; }
        else if( fcnt==0 && bcnt > 0 ) {} // Keep current
        else tied=true;                   // Tied, ambiguous
      }
    }
    assert best_cvts < 99;
    return tied ? null : best_fptr; // Ties need to have the ambiguity broken another way
  }

  // Called from GCP, using the optimistic type.
  public void check_wire( GVNGCM gvn) {
    TypeTuple tcall = (TypeTuple)gvn.type(this);
    Type tfp  = tcall.at(2);
    if( !(tfp instanceof TypeFunPtr) ) return;
    BitsFun fidxs = ((TypeFunPtr)tfp).fidxs();
    check_wire(gvn, fidxs);
  }
  // Used during GCP and Ideal calls to see if wiring is appropriate.
  public boolean check_wire( GVNGCM gvn, BitsFun fidxs ) {
    if( fidxs.above_center() )  return false; // Still choices to be made
    if( gvn._opt_mode == 0 ) return false; // Graph not formed yet
    CallEpiNode cepi = cepi();
    assert cepi!=null;

    // Check all fidxs for being wirable
    boolean progress = false;
    for( int fidx : fidxs ) {                 // For all fidxs
      if( BitsFun.is_parent(fidx) ) continue; // Do not wire parents, as they will eventually settle out
      FunNode fun = FunNode.find_fidx(fidx);  // Lookup, even if not wired
      if( fun.is_forward_ref() ) continue;    // Not forward refs, which at GCP just means a syntax error
      RetNode ret = fun.ret();
      // Internally wire() checks for dups and proper arg counts.
      progress |= cepi.wire(gvn,this,fun,ret);
    }
    assert !progress || Env.START.more_flow(gvn,new VBitSet(),gvn._opt_mode!=2,0)==0; // Post conditions are correct
    return progress;
  }

  @Override public String err(GVNGCM gvn) {
    // Fail for passed-in unknown references directly.
    for( int j=0; j<nargs(); j++ )
      if( arg(j).is_forward_ref() )
        return _badargs.forward_ref_err( FunNode.find_fidx(((FunPtrNode)arg(j)).ret()._fidx) );

    // Expect a function pointer
    Type tfun = gvn.type(fun());
    if( !(tfun instanceof TypeFunPtr) )
      return _badargs.errMsg("A function is being called, but "+tfun+" is not a function type");
    TypeFunPtr tfp = (TypeFunPtr)tfun;

    // Indirectly, forward-ref for function type
    if( tfp.is_forward_ref() ) // Forward ref on incoming function
      return _badargs.forward_ref_err(FunNode.find_fidx(tfp.fidx()));

    // bad-arg-count
    if( tfp.nargs() != nargs() )
      return _badargs.errMsg("Passing "+(nargs()-1)+" arguments to "+tfp.names()+" which takes "+(tfp.nargs()-1)+" arguments");

    // Now do an arg-check.
    // Use self-type not input type, so that we do not depend on a neighbors
    // type.  Neighbors of us can then not depend on a neighbor's neighbor.
    TypeTuple tcall = (TypeTuple)gvn.type(this);
    TypeStruct formals = tfp._args; // Type of each argument
    for( int j=0; j<formals._ts.length; j++ ) {
      Type actual = tcall.at(j+2);
      if( j==0 && actual instanceof TypeFunPtr )
        actual = ((TypeFunPtr)actual).display(); // Extract Display type from TFP
      Type formal = formals.at(j);
      if( !actual.isa(formal) ) // Actual is not a formal
        return _badargs.typerr(actual,formal,mem());
    }

    return null;
  }

  @Override public TypeTuple all_type() {
    Type[] ts = TypeAry.get(_defs._len);
    Arrays.fill(ts,Type.SCALAR);
    ts[0] = Type.CTRL;
    ts[1] = TypeMem.FULL;
    ts[2] = TypeFunPtr.GENERIC_FUNPTR;
    return TypeTuple.make(ts);
  }
  CallEpiNode cepi() {
    for( Node cepi : _uses )    // Find CallEpi for bypass aliases
      if( cepi instanceof CallEpiNode )
        return (CallEpiNode)cepi;
    return null;
  }
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }
  boolean is_copy() { return _is_copy; }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return _is_copy  ? in(idx) : null; }
}
