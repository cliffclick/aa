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
  // Example: call(arg1,arg2)
  // _badargs[1] points to the openning paren.
  // _badargs[2] points to the start of arg1, same for arg2, etc.
  Parse[] _badargs;         // Errors for e.g. wrong arg counts or incompatible args; one error point per arg.
  public CallNode( boolean unpacked, Parse[] badargs, Node... defs ) {
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
  //     be e.g. a Phi or a Load.  This is argument#1, both as the Closure AND
  //     as the Code pointer.
  // 3+  Other "normal" arguments, numbered#2 and up.

  // Number of actual arguments, including the closure/code ptr AND return.
  // This is 2 higher than the user-visible arg count.
  int nargs() { return _defs._len-1; }
  // Argument type
  Type targ( GVNGCM gvn, int x ) {
    Type t = gvn.type(arg(x));
    if( x>0 ) return t;         // Normal argument type
    if( !(t instanceof TypeFunPtr) ) return Type.SCALAR;
    return ((TypeFunPtr)t).display(); // Extract Display type from TFP
  }
  // Actual arguments.  Arg(1) is allowed and refers to the Display/TFP.
  // Arg(0) is the return and is not allowed.
  Node arg( int x ) { assert x>=1; return _defs.at(x+1); }
  // Set an argument.  Use 'set_fun' to set the Display/Code.
  Node set_arg    (int idx, Node arg, GVNGCM gvn) { assert idx>1; return set_def(idx+1,arg,gvn); }
  void set_arg_reg(int idx, Node arg, GVNGCM gvn) { assert idx>1; gvn.set_def_reg(this,idx+1,arg); }

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
    if( tctl!=Type.CTRL ) {     // Dead?
      if( (ctl() instanceof ConNode) ) return null;
      // Kill all inputs with type-safe dead constants
      set_def(1,gvn.con(TypeMem.XMEM),gvn);
      set_def(2,gvn.con(TypeFunPtr.GENERIC_FUNPTR.dual()),gvn);
      if( is_dead() ) return this;
      for( int i=3; i<_defs._len; i++ )
        set_def(i,gvn.con(Type.XSCALAR),gvn);
      gvn.add_work_defs(this);
      return set_def(0,gvn.con(Type.XCTRL),gvn);
    }

    // When do I do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) {          // Not yet unpacked a tuple
      assert nargs()==3;        // The return, Display plus the arg tuple
      Node mem = mem();
      Node arg2 = arg(2);
      Type tadr = gvn.type(arg2);
      // Bypass a merge on the 2-arg input during unpacking
      if( tadr instanceof TypeMemPtr && mem instanceof MemMergeNode ) {
        int alias = ((TypeMemPtr)tadr)._aliases.abit();
        if( alias == -1 ) throw AA.unimpl(); // Handle multiple aliases, handle all/empty
        Node obj = ((MemMergeNode)mem).alias2node(alias);
        if( obj instanceof OProjNode && arg2 instanceof ProjNode && arg2.in(0) instanceof NewNode ) {
          NewNode nnn = (NewNode)arg2.in(0);
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
      return set_fun(FunNode.find_fidx(Math.abs(fidx)).ret().funptr(),gvn);

    // If the function is unresolved, see if we can resolve it now.
    // Fidxs are typically low during iter, but can be high during
    // iter post-GCP on error calls where nothing resolves.
    if( unk instanceof UnresolvedNode && !fidxs.above_center() && !fidxs.test(1)) {
      BitsFun rfidxs = resolve(fidxs,tcall._ts);
      if( rfidxs==null ) return null;            // Dead function, stall for time
      FunPtrNode fptr = least_cost(gvn, rfidxs); // Check for least-cost target
      if( fptr != null ) return set_fun(fptr, gvn); // Resolve to 1 choice
    }

    // Wire targets that are not choices (1 or multi) with matching nargs even
    // with bad/low args; they may lift to good.  CallEpi will inline wired
    // functions with good args.
    if( check_wire(gvn,fidxs) )
      return this;              // Some wiring happened

    // Check for dead args and trim; must be after all wiring is done because
    // unknown call targets can appear during GCP and use the args.  After GCP,
    // still must verify all called functions have the arg as dead, because
    // alive args still need to resolve.  Constants are an issue, because they
    // fold into the Parm and the Call can lose the matching DProj while the
    // arg is still alive.
    if( gvn._opt_mode > 2 && err(gvn)==null ) {
      Node progress = null;
      outer_loop:
      for( int i=2; i<nargs(); i++ ) // Skip the FP/DISPLAY arg, as its useful for error messages
        if( !(arg(i) instanceof ConNode && targ(gvn,i)==Type.XSCALAR) ) { // Not already folded
          for( int fidx2 : fidxs )
            if( FunNode.find_fidx(fidx2).targ(i)!=Type.XSCALAR )
              continue outer_loop; // Fail this arg, as is alive on at least one called function
          progress = set_arg(i,gvn.con(Type.XSCALAR),gvn); // Kill dead arg
        }
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
    // ts[0] = Ctrl = in(0)
    // ts[1] = Mem into the call = in(1)
    // ts[2] = Function pointer (code ptr + display) == in(2) == arg(1)
    // ts[3] = in(3) == arg(2)
    // ts[4]...
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
      mem = mem.above_center() ? TypeMem.XMEM : TypeMem.MEM;
    ts[1] = mem;

    // If not called, then no memory to functions
    if( ctl == Type.XCTRL ) { ts[1] = TypeMem.XMEM; }

    // Copy args for called functions.
    for( int i=1; i<nargs(); i++ )
      ts[i+1] = targ(gvn,i).bound(Type.SCALAR);

    // Not a function to call?
    Type tfx = gvn.type(fun());
    if( !(tfx instanceof TypeFunPtr) )
      tfx = tfx.above_center() ? TypeFunPtr.GENERIC_FUNPTR.dual() : TypeFunPtr.GENERIC_FUNPTR;
    TypeFunPtr tfp = (TypeFunPtr)(ts[2] = tfx);
    BitsFun fidxs = tfp.fidxs();
    // Resolve; only keep choices with sane arguments during GCP
    BitsFun rfidxs = resolve(fidxs,ts);
    if( rfidxs==null ) return (TypeTuple)gvn.self_type(this); // Dead function input, stall until this dies
    if( !rfidxs.test(1) ) { // Neither ANY nor ALL,
      TypeStruct args = tfp._args;
      if( rfidxs == BitsFun.EMPTY ) { // No choices (error)
        args = args.make_from_empty();
      } else { // Unequal function sets; recompute tighter args bounds
        // Meet of remaining function arg types
        args = TypeFunPtr.ARGS.dual();
        for( int fidx : rfidxs )
          args = (TypeStruct)args.meet(FunNode.find_fidx(fidx)._tf._args);
        // Function types always allow nil, so the display can monotonically
        // fall to nil when unused.  If unused, then a nil is passed in and
        // dead in the function.  To preserve monotonicity FPtr, Call and
        // FP2Closure never report a nil possibility.
        TypeMemPtr disp = (TypeMemPtr)args.at(1);
        BitsAlias disp_alias = disp._aliases;
        args = args.set_fld(1,TypeMemPtr.make(disp_alias.strip_nil(),disp._obj),TypeStruct.FFNL);
        if( rfidxs.above_center() )
          args = args.dual();     // Args sign needs to match rfidxs sign
      }
      ts[2] = TypeFunPtr.make(rfidxs,args);
    }
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
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( gvn._opt_mode < 2 ) return super.live_use(gvn,def);
    if( !(def instanceof FunPtrNode) ) return _live;
    int dfidx = ((FunPtrNode)def).ret()._fidx;
    return live_use_call(gvn,dfidx);
  }
  TypeMem live_use_call( GVNGCM gvn, int dfidx ) {
    Type tfx = ((TypeTuple)gvn.type(this)).at(2);
    // If resolve has chosen this dfidx, then the FunPtr is alive.
    return tfx instanceof TypeFunPtr && ((TypeFunPtr)tfx).fidxs().abit() == dfidx
      ? _live : TypeMem.DEAD;
  }


  // Resolve an Unresolved.  Called in value() and so must be monotonic.
  // Strictly looks at arguments and the list of function choices.  Mostly all
  // arguments start in GCP & Iter at the extremes and move towards the center
  // and resolve() cannot move off the extreme until ALL args move.
  // See TestNodeSmall.java for the large mapping table test.
  //
  // Rules "cookbook" to help map the table:
  // - Some args High & no Low, keep all & join (ignore Good,Bad)
  // - Some args Low & no High, keep all & meet (ignore Good,Bad)
  // - Mix High/Low & no Good , keep all
  // - Some Good, no Low, no High, drop Bad & fidx?join:meet
  // - All Bad, like Low: keep all & meet
  private static final int BAD=1, GOOD=2, LOW=4, HIGH=8, DEAD=16;

  BitsFun resolve( BitsFun fidxs, Type[] targs ) {
    if( fidxs==BitsFun.EMPTY) return fidxs; // Nothing to resolve
    if( fidxs==BitsFun.ANY  ) return fidxs; // No point in attempting to resolve all things
    if( fidxs==BitsFun.FULL ) return fidxs; // No point in attempting to resolve all things

    int flags = 0;
    for( int fidx : fidxs )
      flags |= resolve(fidx,targs);
    if( x(flags,DEAD) ) return null; // Caller should stall for time, till dead folds up
    // - Some args High & no Low, keep all & join (ignore Good,Bad)
    if(  x(flags,HIGH) && !x(flags,LOW) ) return sgn(fidxs,true);
    // - Some args Low & no High, keep all & meet (ignore Good,Bad)
    if( !x(flags,HIGH) &&  x(flags,LOW) ) return sgn(fidxs,false);
    // - Mix High/Low, keep all & fidx (ignore Good,Bad)
    if(  x(flags,HIGH) &&  x(flags,LOW) ) return fidxs;
    // - All Bad, like Low: keep all & meet.  Bad args can go dead, effectively lifting.
    if( !x(flags,HIGH) && !x(flags,LOW) && !x(flags,GOOD) && flags!=0 )
      return sgn(fidxs,false);
    // Only had a single target coming in.
    if( fidxs.abit() != -1 ) // Single target
      // If BAD args can die (false in primitives, and false in UnresolvedNodes
      // where the BAD arg is required to make the signature unambiguous) then
      // return all the fidxs, and wait for some arg to die (or else the
      // program is in-error).
      return fidxs;

    // All that is left is the no-args case (all formals ignoring), no high/low
    // and some good and maybe bad.  Toss out the bad & return the remaining
    // fidxs with the same sign.
    BitsFun choices = BitsFun.EMPTY;
    for( int fidx : fidxs )
      if( !x(resolve(fidx,targs),BAD) )
        choices = choices.set(fidx);
    if( choices.abit() != -1 )  // Single choice with all good, no high, no low, no bad
      return choices;           // Report it low
    return sgn(choices,fidxs.above_center());
  }

  private static boolean x(int flags, int flag)  { return (flags&flag)==flag; }
  private static BitsFun sgn(BitsFun fidxs, boolean hi) {
    return fidxs.above_center()==hi ? fidxs : fidxs.dual();
  }

  // Return 4 bools as 4 bits based on whether or not the actual args meets the
  // formals: [High,Low,Good,Bad].  High > formal.dual >= Good >= formal > Low.
  // Bad is none of the prior (actual is neither above nor below the formal).
  int resolve( int fidx, Type[] targs ) {
    if( BitsFun.is_parent(fidx) ) // Parent is never a real choice.  See these during inlining.
      throw com.cliffc.aa.AA.unimpl();

    TypeMem tmem = (TypeMem)targs[1]; // Call Memory
    FunNode fun = FunNode.find_fidx(fidx);
    if( fun==null || fun.is_dead() ) return DEAD; // Stale fidx leading to dead fun
    // Forward refs are only during parsing; assume they fit the bill
    if( fun.is_forward_ref() ) return HIGH;    // Assume they work
    if( fun.nargs() != nargs() ) return BAD;   // Wrong arg count, toss out
    TypeStruct formals = fun._tf._args;        // Type of each argument
    int flags=0;
    for( int j=1; j<nargs(); j++ ) {        // Skip 0, the function return
      Type formal = formals.at(j);
      if( formal.above_center() ) continue; // Arg is ignored
      Type actual = targs[j+1];             // Calls skip ctrl & mem
      if( j==1 && actual instanceof TypeFunPtr )
        actual = ((TypeFunPtr)actual).display(); // Extract Display type from TFP
      assert actual==actual.simple_ptr();        // Only simple ptrs from nodes
      actual = actual.sharpen(tmem);             // Sharpen actual pointers before checking vs formals

      if( actual==formal ) { flags|=GOOD; continue; } // Arg is fine.  Covers NO_DISP which can be a high formal.
      Type mt_lo = actual.meet(formal       );
      Type mt_hi = actual.meet(formal.dual());
      if( mt_lo==actual ) flags|=LOW;       // Low
      else if( mt_hi==actual ) flags|=GOOD; // Good
      else if( mt_hi==formal.dual() ) flags|=HIGH;
      else if( mt_lo==formal ) flags|=GOOD; // handles some display cases with prims hi/lo inverted
      else flags|=BAD;                      // Side-ways is bad
    }

    return flags;
  }


  // Amongst these choices return the least-cost.  Some or all might be
  // invalid.
  public FunPtrNode least_cost(GVNGCM gvn, BitsFun choices) {
    if( choices==BitsFun.EMPTY ) return null;
    assert choices.bitCount() > 0; // Must be some choices
    assert choices.above_center() == (gvn._opt_mode==2);
    int best_cvts=99999;           // Too expensive
    FunPtrNode best_fptr=null;     //
    TypeStruct best_formals=null;  //
    boolean tied=false;            // Ties not allowed
    for( int fidx : choices ) {
      if( BitsFun.is_parent(fidx) ) throw com.cliffc.aa.AA.unimpl();

      FunNode fun = FunNode.find_fidx(fidx);
      if( fun.nargs()!=nargs() || fun.ret() == null ) continue; // BAD/dead
      TypeStruct formals = fun._tf._args; // Type of each argument
      int cvts=0;                         // Arg conversion cost
      for( int j=2; j<nargs(); j++ ) {    // Skip arg#0, the return and #1 the display
        Type actual = targ(gvn,j);
        Type formal = formals.at(j);
        if( actual==formal ) continue;
        if( formal.above_center() ) continue; // Formal is ignored
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
        for( int i=0; i<formals._ts.length; i++ ) {
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
    if( best_cvts >= 99 ) return null; // No valid functions
    return tied ? null : best_fptr; // Ties need to have the ambiguity broken another way
  }

  // Called from GCP, using the optimistic type.
  public void check_wire( GVNGCM gvn) {
    TypeTuple tcall = (TypeTuple)gvn.type(this);
    if( tcall.at(0) != Type.CTRL ) return;
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
      // Internally wire() checks for already wired.
      progress |= cepi.wire(gvn,this,fun,ret);
    }
    assert !progress || Env.START.more_flow(gvn,new VBitSet(),gvn._opt_mode!=2,0)==0; // Post conditions are correct
    return progress;
  }

  @Override public String err(GVNGCM gvn) { return err(gvn,false); }
  String err(GVNGCM gvn, boolean fast) {
    // Fail for passed-in unknown references directly.
    for( int j=1; j<nargs(); j++ )
      if( arg(j).is_forward_ref() )
        return fast ? "" : _badargs[j].forward_ref_err( FunNode.find_fidx(((FunPtrNode)arg(j)).ret()._fidx) );

    // Expect a function pointer
    Type tfun = gvn.type(fun());
    if( !(tfun instanceof TypeFunPtr) )
      return fast ? "" : _badargs[1].errMsg("A function is being called, but "+tfun+" is not a function type");
    TypeFunPtr tfp = (TypeFunPtr)tfun;

    // Indirectly, forward-ref for function type
    if( tfp.is_forward_ref() ) // Forward ref on incoming function
      return _badargs[1].forward_ref_err(FunNode.find_fidx(tfp.fidx()));
    if( tfp.fidxs().is_empty() )
      return null; // This is an unresolved call, and that error is reported elsewhere

    // bad-arg-count
    if( tfp.nargs() != nargs() )
      return fast ? "" : _badargs[1].errMsg("Passing "+(nargs()-2)+" arguments to "+tfp.names()+" which takes "+(tfp.nargs()-2)+" arguments");

    // Now do an arg-check.
    TypeStruct formals = tfp._args; // Type of each argument
    for( int j=2; j<nargs(); j++ ) {
      Type actual = gvn.sharptr(arg(j),mem());
      Type formal = formals.at(j);
      if( formal==Type.XSCALAR ) continue; // Formal is dead
      if( !actual.isa(formal) ) { // Actual is not a formal
        if( fast ) return "";
        if( tfp.fidxs().abit() != -1 )
          return _badargs[j].typerr(actual,null,formal);
        // Multiple fails.  Try for a better error message.
        Type[] ts = new Type[tfp.fidxs().bitCount()];
        int i=0;
        for( int fidx : tfp.fidxs() ) {
          FunNode fun = FunNode.find_fidx(fidx);
          ts[i++] = fun.targ(j);
        }
        return _badargs[j].typerr(actual,null,ts);
      }
    }

    return null;
  }

  @Override public TypeTuple all_type() {
    Type[] ts = TypeAry.get(_defs._len);
    Arrays.fill(ts,Type.SCALAR);
    ts[0] = Type.CTRL;
    ts[1] = TypeMem.MEM;
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
