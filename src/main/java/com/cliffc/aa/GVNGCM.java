package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

import java.util.BitSet;

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
  private final Work _work_dead   = new Work("dead"  , false) { @Override public Node apply(Node n) { return n._uses._len == 0 ? n.kill() : null; } };
  private final Work _work_reduce = new Work("reduce", true ) { @Override public Node apply(Node n) { return n.do_reduce(); } };
  private final Work _work_flow   = new Work("flow"  , false) { @Override public Node apply(Node n) { return n.do_flow  (); } };
  private final Work _work_mono   = new Work("mono"  , true ) { @Override public Node apply(Node n) { return n.do_mono  (); } };
  private final Work _work_grow   = new Work("grow"  , true ) { @Override public Node apply(Node n) { return n.do_grow  (); } };
  private final Work _work_inline = new Work("inline", false) { @Override public Node apply(Node n) { return ((FunNode)n).ideal_inline(false); } };
  public  final Work _work_dom    = new Work("dom"   , false) { @Override public Node apply(Node n) { return n.do_mono  (); } };
  @SuppressWarnings("unchecked")
  private final Work[]    _new_works = new Work[]{           _work_flow,_work_reduce,_work_mono,_work_grow             };
  @SuppressWarnings("unchecked")
  public  final Work[] _reduce_works = new Work[]{_work_dead,_work_flow,_work_reduce                                    };
  @SuppressWarnings("unchecked")
  private final Work[]    _all_works = new Work[]{_work_dead,_work_flow,_work_reduce,_work_mono,_work_grow,_work_inline};
  static private boolean HAS_WORK;
  public boolean on_dead  ( Node n ) { return _work_dead  .on(n); }
  public boolean on_flow  ( Node n ) { return _work_flow  .on(n); }
  public boolean on_reduce( Node n ) { return _work_reduce.on(n); }

  static public <N extends Node> N add_work( Work work, N n ) {
    if( n.is_dead() ) return n;
    if( !HAS_WORK ) HAS_WORK = true; // Filtered set
    return work.add(n);
  }
  public void add_dead  ( Node n ) { add_work(_work_dead, n); }
  public <N extends Node> N add_reduce( N n ) { return add_work(_work_reduce,n); }
  public <N extends Node> N add_flow  ( N n ) { return add_work(_work_flow  ,n); }
  public <N extends Node> N add_mono  ( N n ) { return add_work(_work_mono  ,n); }
  public void add_grow  ( Node n ) { add_work(_work_grow  ,n); }
  public void add_inline( FunNode n ) { add_work(_work_inline, n); }
  public void add_flow_defs  ( Node n ) { add_work_defs(_work_flow  ,n); }
  public void add_flow_uses  ( Node n ) { add_work_uses(_work_flow  ,n); }
  public void add_flow  ( Ary<TNode> deps ) { if( deps != null ) for( TNode dep : deps )  add_flow((Node)dep); }
  public void add_flow_uses( Ary<TNode> deps ) {
    if( deps != null )
      for( TNode dep : deps )
        if( !dep.is_dead() )
          for( Node use : ((Node)dep)._uses )
            add_flow(use).add_flow_use_extra((Node)dep);
  }
  public void add_reduce_uses( Node n ) { add_work_uses(_work_reduce,n); }
  // n goes unused
  public Node add_unuse( Node n ) {
    if( n._uses._len==0 && n._keep==0 ) { add_dead(n); return n; } // might be dead
    return add_reduce(add_flow(n));
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
    if( n.is_dead() ) return n;
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
  public <N extends Node> N init( N n ) { return add_flow(add_reduce(n.keep())); }

  // Did a bulk not-monotonic update.  Forcibly update the entire region at
  // once; restores monotonicity over the whole region when done.
  public void revalive(Node... ns) {
    for( Node n : ns )  if( n != null )  n.reset_tvar();
    for( Node n : ns )  if( n != null )  n.unify(false);
    revalive2(ns);
  }
  // Bulk not-monotonic update, without reseting tvars
  public void revalive2(Node... ns) {
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
    assert n._uses._len==0 && n._keep==0; // New to GVN
    Node x = iter(add_work_all(n),_all_works);
    if( x==null ) x=n;          // Ignore lack-of-progress
    return add_flow(x);         // No liveness (yet), since uses not known
  }

  // Apply graph-rewrite rules, up to the ideal_reduce calls.  Return a node
  // that is possibly "more ideal" than what was before.
  public Node xreduce( Node n ) {
    assert n._uses._len==0 && n._keep==0; // New to GVN
    Node x = iter(add_work_all(n), _reduce_works);
    if( x==null ) x=n;          // Ignore lack-of-progress
    return add_flow(x);         // No liveness (yet), since uses not known
  }


  // Top-level iter cleanout.  Changes GVN modes & empties all queues &
  // aggressively checks no-more-progress.
  private static final VBitSet IDEAL_VISIT = new VBitSet();
  public void iter(Mode opt_mode) {
    _opt_mode = opt_mode;
    boolean progress=true;
    while( progress ) {
      progress = false;
      iter(null,_all_works);
      // Only a very few nodes can make progress via dominance relations, and
      // these can make progress "very far" in the graph.  So instead of using
      // a neighbors list, we bulk revisit them here.
      for( int i=0; i<_work_dom.len(); i++ ) {
        Node dom = _work_dom.at(i);
        if( dom.is_dead() ) _work_dom.del(i--);
        else progress |= _work_dom.apply(dom)!=null;
      }
    }
    IDEAL_VISIT.clear();
    // Expensive assert
    assert !Env.START.more_ideal(IDEAL_VISIT);
  }

  // Any time anything is on any worklist we can always conservatively iterate on it.
  // Return null if no progress.  Otherwise return 'n' or a replacement for 'n'.
  static int ITER_CNT;
  static int ITER_CNT_NOOP;
  static int ITER_NEST=0;
  public Node iter(Node x, Work[] works) {
    if( _opt_mode== Mode.Pause ) return x;
    if( !HAS_WORK ) return x;
    if( x!=null ) x.keep(); // Always keep this guy, unless reducing it directly
    ITER_NEST++;
    Work outer = null;
    boolean progress=false;
    outer:
    while( true ) {
      for( Work W : works ) {
        Node n = W.pop();
        if( n==null ) continue; // Worklist is empty
        if( n.is_dead() ) { ITER_CNT_NOOP++; continue outer; }
        boolean keep = x==n && W._replacing; // Allow X to be replaced
        if( keep ) x.unkeep();               // Need to upgrade X in-place
        if( n._keep>0 && W._replacing && ITER_NEST > 1 ) { // Will not upgrade in this iter, but may be in a recursive iter
          if( outer==null ) outer = new Work("outer",true) { @Override public Node apply(Node n) { throw com.cliffc.aa.AA.unimpl(); } };
          outer.add(n);         // Save for a recursive iter
        }
        Node m = W.apply(n);
        if( m == null ) {       // not-null is progress
          ITER_CNT_NOOP++;      // No progress
        } else {
          // VERY EXPENSIVE ASSERT
          //assert W==_work_dead || Env.START.more_flow(true)==0; // Initial conditions are correct
          ITER_CNT++; assert ITER_CNT < 35000; // Catch infinite ideal-loops
          if( x==n ) x=m;       // Keep track of the replacement for x, if any
          progress = true;      // flag progress
        }
        if( keep ) x.keep();
        continue outer;
      }
      HAS_WORK=false;
      Node.roll_back_CNT();     // Can reclaim node numbers
      if( x!=null ) x.unkeep();
      if( outer!=null && progress )
        for( Node n : outer._work ) add_reduce(n);
      ITER_NEST--;
      return progress ? x : null;
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
          n.add_flow_extra(oval);
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
    Env.START.walk_opt(visit);
  }

  private void remove_ambi( CallNode call ) {
    TypeFunPtr tfp = CallNode.ttfpx(call._val);
    FunPtrNode fptr = null;
    BitsFun fidxs = tfp.fidxs();
    if( !fidxs.above_center() ) return; // Resolved after all
    if( fidxs!=BitsFun.ANY ) {          // And have choices
      // Pick least-cost among choices
      fptr = call.least_cost(fidxs,call.fdx());
      if( fptr==null ) { // Not resolving, program is in-error
        call._not_resolved_by_gcp = true; // will drop fdx in lattice
        add_flow(call);
        return;
      }
    }
    call.set_dsp(fptr.display());
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

  // Walk all memory edges, and 'retype' them, probably DOWN (counter to
  // 'iter').  Used when inlining, and the inlined body needs to acknowledge
  // bypasses aliases.  Used during code-clone, to lift the split alias parent
  // up & out.
  public static void retype_mem( BitSet aliases, Node mem, Node exit, boolean skip_calls ) {
    Ary<Node> work = new Ary<>(new Node[1],0);
    work.push(mem);
    // Update all memory ops
    while( !work.isEmpty() ) {
      Node wrk = work.pop();
      if( !wrk.is_mem() && wrk!=mem ) continue; // Not a memory Node?
      Type twrk = wrk._val;
      Type tmem0 = twrk instanceof TypeTuple ? ((TypeTuple)twrk).at(1) : twrk;
      if( !(tmem0 instanceof TypeMem) ) continue; // Node does have have a memory type?
      if( aliases!=null && !((TypeMem)tmem0).has_used(aliases) ) continue; // Not does not use the listed memory?
      if( wrk instanceof CallNode ) { // Do the CEPI for a Call, skipping in-between
        CallEpiNode cepi = ((CallNode)wrk).cepi();
        if( cepi != null ) work.push(cepi);
      }
      Type tval = wrk.value(Env.GVN._opt_mode); // Recompute memory value
      if( twrk == tval ) continue;              // No change
      wrk._val = tval;                          // Progress!!!
      Env.GVN.add_flow_uses(wrk);               // Forwards flow the update
      if( wrk==exit ) continue;                 // Stop at end
      if( skip_calls && wrk instanceof MProjNode && wrk.in(0) instanceof CallNode )
        continue;               // Skip the inside of calls
      work.addAll(wrk._uses);
    }
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
      iter((Node)null,_reduce_works); // Cleanup
      if( _ret!=null ) _ret.unkeep();
    }
  }
}
