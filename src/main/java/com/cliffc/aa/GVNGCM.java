package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

// Global Value Numbering, Global Code Motion
public class GVNGCM {

  public enum Mode {
    Parse   (false),          // Parsing
    PesiNoCG(false),          // Lifting, unknown Call Graph
    Opto    (true ),          // Falling, Call Graph discovery, no more code
    PesiCG  (true ),          // Lifting,   known Call Graph
    Pause   (false);          // Do not iter()
    public final boolean _CG; // True if full CG is known or being discovered.  Only for whole programs during or after Opto.
    Mode(boolean CG) { _CG=CG; }
  }
  public Mode _opt_mode=Mode.Parse;

  // Iterative worklists.
  private final Work _work_dead   = new Work("dead"  ) { @Override public Node apply(Node n) { return n._uses._len == 0 ? n.kill() : null; } };
  private final Work _work_reduce = new Work("reduce") { @Override public Node apply(Node n) { return n.do_reduce(); } };
  private final Work _work_flow   = new Work("flow"  ) { @Override public Node apply(Node n) { return n.do_flow  (); } };
  private final Work _work_mono   = new Work("mono"  ) { @Override public Node apply(Node n) { return n.do_mono  (); } };
  private final Work _work_grow   = new Work("grow"  ) { @Override public Node apply(Node n) { return n.do_grow  (); } };
  private final Work _work_inline = new Work("inline") { @Override public Node apply(Node n) { return ((FunNode)n).ideal_inline(false); } };
  @SuppressWarnings("unchecked")
  private final Work[] _new_works = new Work[]{           _work_flow,_work_reduce,_work_mono,_work_grow             };
  @SuppressWarnings("unchecked")
  private final Work[] _all_works = new Work[]{_work_dead,_work_flow,_work_reduce,_work_mono,_work_grow,_work_inline};
  static private boolean HAS_WORK;
  public boolean on_dead  ( Node n ) { return _work_dead  .on(n); }
  public boolean on_flow  ( Node n ) { return _work_flow  .on(n); }
  public boolean on_reduce( Node n ) { return _work_reduce.on(n); }

  static public <N extends Node> N add_work( Work work, N n ) {
    if( !HAS_WORK ) HAS_WORK = true; // Filtered set
    return work.add(n);
  }
  public void add_dead  ( Node n ) { add_work(_work_dead, n); }
  public <N extends Node> N add_reduce( N n ) { return add_work(_work_reduce,n); }
  public <N extends Node> N add_flow  ( N n ) { return add_work(_work_flow  ,n); }
  public void add_grow  ( Node n ) { add_work(_work_grow  ,n); }
  public void add_inline( FunNode n ) { add_work(_work_inline, n); }
  public void add_flow_defs  ( Node n ) { add_work_defs(_work_flow  ,n); }
  public void add_flow_uses  ( Node n ) { add_work_uses(_work_flow  ,n); }
  public void add_reduce_uses( Node n ) { add_work_uses(_work_reduce,n); }
  // n goes unused
  public void add_unuse( Node n ) {
    if( n._uses._len==0 && n._keep==0 ) { add_dead(n); return; } // might be dead
    add_reduce(add_flow(n));
  }
  static public void add_work_defs( Work work, Node n ) {
    for( Node def : n._defs )
      if( def != null && def != n )
        add_work(work,def);
  }
  static public void add_work_uses( Work work, Node n ) {
    for( Node use : n._uses )
      if( use != n )
        add_work(work,use);
  }
  public Node add_work_all( Node n ) {
    if( !HAS_WORK ) HAS_WORK = true; // Filtered set
    for( Work work : _new_works ) work.add(n);
    if( n instanceof FunNode )
        add_work(_work_inline,(FunNode)n);
    return n;
  }

  // Initial state after loading e.g. primitives.
  void init0() {
    for( Work work : _all_works ) assert work.isEmpty();
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  void reset_to_init0() {
    for( Work work : _all_works ) work.clear();
    _opt_mode = Mode.Parse;
    ITER_CNT = ITER_CNT_NOOP = 0;
  }

  // Record a Node, but do not optimize it for value and ideal calls, as it is
  // mid-construction from the parser.  Any function call with yet-to-be-parsed
  // call sites, and any loop top with an unparsed backedge needs to use this.
  public <N extends Node> N init( N n ) { return add_reduce(n.keep()); }

  // Did a bulk not-monotonic update.  Forcibly update the entire region at
  // once; restores monotonicity over the whole region when done.
  public void revalive(Node... ns) {
    for( Node n : ns ) {
      if( n == null ) continue;
      Type t = n.value(_opt_mode);
      if( t != n._val ) {
        n._val = t;
        add_flow_uses(n);
      }
    }
    for( int i=ns.length-1; i>=0; i-- ) {
      Node n = ns[i];
      if( n==null ) continue;
      TypeMem t = n.live(_opt_mode);
      if( t != n._live ) {
        n._live=t;
        add_flow_defs(n);
      }
    }
  }

  // Apply graph-rewrite rules on new nodes (those with no users and kept alive
  // for the parser).  Return a node registered with GVN that is possibly "more
  // ideal" than what was before.
  public Node xform( Node n ) {
    assert n._uses._len==0;     // New to GVN
    assert n._keep==0;
    n.keep();
    Node progress = n;
    while( progress!=null ) {
      progress = n.do_flow();
      n.unkeep();
      Node x;
      if( (x=n.do_reduce()) != null ) { n=x; progress=n; }
      if( (x=n.do_mono  ()) != null ) { n=x; progress=n; }
      if( (x=n.do_grow  ()) != null ) { n=x; progress=n; }
      n.keep();
      if( iter() ) progress=n;
    }
    if( n instanceof FunNode ) add_inline((FunNode)n);
    n.unkeep();
    add_flow(n); // if keep falls back to zero; next time can compute proper liveness
    return n;
  }

  private static final VBitSet IDEAL_VISIT = new VBitSet();
  public boolean iter(Mode opt_mode) {
    _opt_mode = opt_mode;
    boolean progress = iter();
    IDEAL_VISIT.clear();
    assert !Env.START.more_ideal(IDEAL_VISIT);
    return progress;
  }

  // Once the program is complete, any time anything is on the worklist we can
  // always conservatively iterate on it.
  static int ITER_CNT;
  static int ITER_CNT_NOOP;
  public boolean iter() {
    if( _opt_mode== Mode.Pause ) return false;
    if( !HAS_WORK ) return false;
    boolean progress = false;
    outer:
    while( true ) {
      for( Work W : _all_works ) {
        Node n = W.pop();
        if( n==null ) continue;
        if( !n.is_dead() && W.apply(n) !=null ) {
          // VERY EXPENSIVE ASSERT
          //assert W==_work_dead || Env.START.more_flow(true)==0; // Initial conditions are correct
          ITER_CNT++; assert ITER_CNT < 35000; // Catch infinite ideal-loops
          progress = true;
        } else {
          ITER_CNT_NOOP++;      // No progress
        }
        continue outer;
      }
      HAS_WORK=false;
      return progress;
    }
  }

  // Global Optimistic Constant Propagation.  Passed in the final program state
  // (including any return result, i/o & memory state).  Returns the most-precise
  // types possible, and replaces constants types with constants.
  //
  // Besides the obvious GCP algorithm (and the type-precision that results
  // from the analysis), GCP does a few more things.
  //
  // GCP builds an explicit Call-Graph.  Before GCP not all callers are known
  // and this is approximated by being called by ALL_CTRL, a ConNode of Type
  // CTRL, as a permanently available unknown caller.  If the whole program is
  // available to us then we can compute all callers conservatively and fairly
  // precisely - we may have extra never-taken caller/callee edges, but no
  // missing caller/callee edges.  These edges are virtual (represented by
  // ALL_CTRL) before GCP.  Just before GCP we remove the ALL_CTRL path, and
  // during GCP we add in physical CG edges as possible calls are discovered.
  //
  // GCP resolves all ambiguous (overloaded) calls, using the precise types
  // first, and then inserting conversions using a greedy decision.  If this is
  // not sufficient to resolve all calls, the program is ambiguous and wrong.
  public void gcp(Mode mode, ScopeNode rez ) {
    _opt_mode = mode;
    // Set all values to ALL and lives to DEAD, their most optimistic types.
    VBitSet visit = new VBitSet();
    Env.START.walk_initype(this,visit);
    assert Env.START.more_flow(false)==0; // Initial conditions are correct
    // Collect unresolved calls, and verify they get resolved.
    Ary<CallNode> ambi_calls = new Ary<>(new CallNode[1],0);

    // Repeat, if we remove some ambiguous choices, and keep falling until the
    // graph stabilizes without ambiguity.
    while( !_work_flow.isEmpty() ) {
      // Analysis phase.
      // Work down list until all reachable nodes types quit falling
      Node n;
      while( (n=_work_flow.pop()) != null ) {
        if( n.is_dead() ) continue; // Can be dead functions after removing ambiguous calls

        // Forwards flow
        Type oval = n._val;                                // Old local type
        Type nval = n.value(_opt_mode);                    // New type
        if( oval != nval ) {                               // Progress
          if( check_not_monotonic(n, oval, nval) ) continue; // Debugging hook
          n._val = nval;            // Record progress
          for( Node use : n._uses ) // Classic forwards flow on change
            add_flow(use).add_flow_use_extra(n);
          if( n instanceof CallEpiNode ) check_and_wire((CallEpiNode)n);
          for( Node use : n._uses )
            if( use instanceof CallEpiNode ) check_and_wire((CallEpiNode)use);
        }

        // Reverse flow
        TypeMem oliv = n._live;
        TypeMem nliv = n.live(_opt_mode);
        if( oliv != nliv ) {      // Liveness progress
          if( check_not_monotonic(n, oliv, nliv) ) continue; // Debugging hook
          n._live = nliv;           // Record progress
          for( Node def : n._defs ) // Classic reverse flow on change
            if( def!=null ) add_flow(def).add_flow_def_extra(n);
        }
        // See if we can resolve an unresolved
        if( n instanceof CallNode && n._live != TypeMem.DEAD ) {
          CallNode call = (CallNode)n;
          if( call.ctl().val() == Type.CTRL && call.val() instanceof TypeTuple ) { // Wait until the Call is reachable
            // Track ambiguous calls: resolve after GCP gets stable, and if we
            // can resolve we continue to let GCP fall.
            BitsFun fidxs = CallNode.ttfp(call.val()).fidxs();
            if( fidxs.above_center() && fidxs.abit() == -1 && ambi_calls.find(call) == -1 )
              ambi_calls.add(call);
            // If the function input can never fall to any function type, abort
            // the resolve now.  The program is in-error.
            if( !call.fdx().val().isa(TypeFunPtr.GENERIC_FUNPTR) ) {
              call._not_resolved_by_gcp = true;
              add_work(_work_flow,call);
            }
          }
        }
        // Very expensive assert
        //assert Env.START.more_flow(false)==0; // Initial conditions are correct
      }

      // Remove CallNode ambiguity after worklist runs dry.  This makes a
      // 'least_cost' choice on unresolved Calls, and lowers them in the
      // lattice... allowing more GCP progress.
      while( !ambi_calls.isEmpty() )
        remove_ambi(ambi_calls.pop());
    }

    assert Env.START.more_flow(false)==0; // Final conditions are correct
    visit.clear();
    rez.walk_opt(visit);
  }

  private void remove_ambi( CallNode call ) {
    TypeFunPtr tfp = CallNode.ttfpx(call.val());
    FunPtrNode fptr = null;
    if( tfp != null ) {     // Have a sane function ptr?
      BitsFun fidxs = tfp.fidxs();
      if( !fidxs.above_center() ) return; // Resolved after all
      if( fidxs!=BitsFun.ANY )            // And have choices
        // Pick least-cost among choices
        fptr = call.least_cost(fidxs,call.fdx());
    }
    if( fptr==null ) {          // Not resolving, program is in-error
      call._not_resolved_by_gcp = true;
      //add_work(call);
      //add_work(call.fdx());
      //return;                   // Not resolving, but Call flagged as in-error
      throw com.cliffc.aa.AA.unimpl();
    }
    call.set_def(AA.FUN_IDX,fptr.display());
    call.set_fdx(fptr);         // Set resolved edge
    add_flow(call);
    assert Env.START.more_flow(false)==0; // Post conditions are correct
  }

  private void check_and_wire( CallEpiNode cepi ) {
    if( !cepi.check_and_wire() ) return;
    assert Env.START.more_flow(false)==0;
  }

  // Debugging hook
  private boolean check_not_monotonic( Node n, Type ot, Type nt) {
    assert nt==nt.simple_ptr();   // Only simple pointers in node types
    if( ot.isa(nt) ) return false; // No bug
    add_flow(n);                  // Setup for a re-run
    System.out.println("Not monotonic");
    return true;    // Just single-step forward in debugging to re-run n.value
  }

  public class Build<N extends Node> implements AutoCloseable {
    Ary<Node> _tmps = new Ary<>(new Node[1],0);
    public N _ret;
    public Node xform( Node n ) {
      Node x = n.do_reduce();   // Attempt to reduce
      return init(x==null ? n : x);
    }
    public Node init( Node n ) {
      assert _tmps._len<16;             // Time for a BitSet
      if( _tmps.find(n)!=-1 ) return n; // Already flowed & keeped
      n.keep().do_flow(); // Update types, and future Parser uses, so always alive
      return _tmps.push(n);
    }
    public Node add( Node n ) {
      assert _tmps._len<16;             // Time for a BitSet
      if( _tmps.find(n)!=-1 ) return n; // Already flowed & keeped
      return _tmps.push(n.keep());
    }
    @SuppressWarnings("unchecked")
    public <M extends Node> M init2( M n ) { return (M)init(n); }
    @Override public void close() {
      if( _ret!=null ) _ret.keep(); // Thing being returned at close-point is always alive
      for( Node tmp : _tmps )
        add_unuse(tmp.unkeep()); // Needs proper liveness at least
      iter();                    // Cleanup
      if( _ret!=null ) _ret.unkeep();
    }
  }
}
