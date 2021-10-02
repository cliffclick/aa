package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.UQNodes;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

import java.util.BitSet;

import static com.cliffc.aa.AA.unimpl;

// Global Value Numbering, Global Code Motion
public class GVNGCM {

  public enum Mode {
    Parse   (false),          // Parsing
    PesiNoCG(false),          // Lifting, unknown Call Graph
    Opto    (true ),          // Falling, Call Graph discovery, no more code
    PesiCG  (true );          // Lifting,   known Call Graph
    public final boolean _CG; // True if full CG is known or being discovered.  Only for whole programs during or after Opto.
    Mode(boolean CG) { _CG=CG; }
  }
  public Mode _opt_mode=Mode.Parse;

  // Iterative worklists.
  private final Work _work_dead   = new Work("dead"  , false) { @Override public Node apply(Node n) { return n._keep==0 && n._uses._len == 0 ? n.kill() : null; } };
  private final Work _work_reduce = new Work("reduce", true ) { @Override public Node apply(Node n) { return n.do_reduce(); } };
  public  final Work _work_flow   = new Work("flow"  , false) { @Override public Node apply(Node n) { return n.do_flow  (); } };
  private final Work _work_mono   = new Work("mono"  , true ) { @Override public Node apply(Node n) { return n.do_mono  (); } };
  private final Work _work_grow   = new Work("grow"  , true ) { @Override public Node apply(Node n) { return n.do_grow  (); } };
  private final Work _work_inline = new Work("inline", false) { @Override public Node apply(Node n) { return ((FunNode)n).ideal_inline(false); } };
  public  final Work _work_dom    = new Work("dom"   , false) { @Override public Node apply(Node n) { return n.do_mono  (); } };
  private final Work[]    _new_works = new Work[]{           _work_flow,_work_reduce,_work_mono,_work_grow             };
  private final Work[]    _all_works = new Work[]{_work_dead,_work_flow,_work_reduce,_work_mono,_work_grow,_work_inline};
  static private boolean HAS_WORK;
  public boolean on_dead  ( Node n ) { return _work_dead  .on(n); }

  static public <N extends Node> N add_work( Work work, N n ) {
    if( n==null || n.is_dead() ) return n;
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
  public void add_flow( UQNodes deps ) { if( deps != null ) for( Node dep : deps.values() ) add_flow(dep); }
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
    if( n.is_dead() ) return n;
    if( !HAS_WORK ) HAS_WORK = true; // Filtered set
    for( Work work : _new_works ) work.add(n);
    if( n instanceof FunNode )
      add_work(_work_inline,(FunNode)n);
    return n;
  }

  // Initial state after loading e.g. primitives.
  void init0() {
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  void reset_to_init0() {
    for( Work work : _all_works ) work.clear();
    _work_dom.clear();
    HAS_WORK = true;
    _opt_mode = Mode.Parse;
    ITER_CNT = ITER_CNT_NOOP = 0;
  }

  // Record a Node, but do not optimize it for value and ideal calls, as it is
  // mid-construction from the parser.  Any function call with yet-to-be-parsed
  // call sites, and any loop top with an unparsed backedge needs to use this.
  public <N extends Node> N init( N n ) { return add_flow(add_reduce(n.keep(2))); }

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
    assert n._uses._len==0 && n._keep==0; // New to GVN
    Node x = iter(add_work_all(n),_all_works);
    assert !x.is_dead();
    return add_flow(x);         // No liveness (yet), since uses not known
  }

  // Apply graph-rewrite rules, up to the ideal_reduce calls.  Return a node
  // that is possibly "more ideal" than what was before.
  public Node xreduce( Node n ) {
    assert n._uses._len==0 && n._keep==0; // New to GVN
    n.do_flow();                // Compute _val (for finding constants)
    Node x = n.do_reduce();     // Maybe find a more ideal Node
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
  // Empties the worklist, attempting to do every possible thing.
  // Returns 'x' or a replacement for 'x'.
  static int ITER_CNT;
  static int ITER_CNT_NOOP;
  public Node iter(Node x, Work[] works) {
    if( !HAS_WORK ) return x;
    if( x!=null ) x.keep();
    while( true ) {
      Work W=null;
      for( Work work : works )
        if( !(W = work).isEmpty() )
          break;
      if( W.isEmpty() ) break;      // All worklists empty
      Node n = W.pop();
      Node m = n.is_dead() ? null : W.apply(n);
      if( m == null ) {       // not-null is progress
        ITER_CNT_NOOP++;      // No progress
      } else {
        // VERY EXPENSIVE ASSERT
        //assert W==_work_dead || Env.START.more_flow(_work_flow,true)==0; // Initial conditions are correct
        ITER_CNT++; assert ITER_CNT < 35000; // Catch infinite ideal-loops
        if( x==n ) x=m;       // Keep track of the replacement for x, if any
      }
    }
    HAS_WORK=false;
    Node.roll_back_CNT();       // Can reclaim node numbers
    if( x==null ) return null;  // No special node to track
    return x.unkeep();
  }

  public void iter_dead() {
    Node n;
    while( (n=_work_dead.pop()) != null )
      _work_dead.apply(n);
  }

  // Walk all memory edges, and 'retype' them, probably DOWN (counter to
  // 'iter').  Used when inlining, and the inlined body needs to acknowledge
  // bypasses aliases.  Used during code-clone, to lift the split alias parent
  // up & out.
  private static final Work WORK_RETYPE = new Work("retype",false) { @Override public Node apply( Node n) { throw unimpl(); } };
  public static void retype_mem( BitSet aliases, Node mem, Node exit, boolean skip_calls ) {
    WORK_RETYPE.add(mem);
    // Update all memory ops
    while( !WORK_RETYPE.isEmpty() ) {
      Node wrk = WORK_RETYPE.pop();
      if( !(wrk instanceof CallNode) && !wrk.is_mem() && wrk!=mem ) continue; // Not a memory Node?
      Type twrk = wrk._val;
      Type tmem0 = twrk instanceof TypeTuple ? ((TypeTuple)twrk).at(1) : twrk;
      if( !(tmem0 instanceof TypeMem) ) continue; // Node does have a memory type?
      if( aliases!=null && !((TypeMem)tmem0).has_used(aliases) ) continue; // Does not use the listed memory?
      if( wrk instanceof CallNode ) { // Do the CEPI for a Call, skipping in-between
        CallEpiNode cepi = ((CallNode)wrk).cepi();
        if( cepi != null ) WORK_RETYPE.add(cepi);
      }
      Type tval = wrk.value(Env.GVN._opt_mode); // Recompute memory value
      if( twrk == tval ) continue;              // No change
      wrk._val = tval;                          // Progress!!!
      Env.GVN.add_flow_uses(wrk);               // Forwards flow the update
      if( wrk==exit ) continue;                 // Stop at end
      if( skip_calls && wrk instanceof MProjNode && wrk.in(0) instanceof CallNode )
        continue;               // Skip the inside of calls
      // Retype function signatures as well
      if( wrk instanceof RetNode || wrk instanceof ParmNode ) {
        FunNode fun = wrk instanceof RetNode ? ((RetNode)wrk).fun() : (FunNode)wrk.in(0);
        fun._sig = fun.re_sig();
      }

      WORK_RETYPE.add(wrk._uses);
    }
    assert Env.START.more_flow(Env.GVN._work_flow,true)==0;
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
      for( Node tmp : _tmps )
        add_unuse(tmp.unkeep()); // Needs proper liveness at least
    }
  }
}
