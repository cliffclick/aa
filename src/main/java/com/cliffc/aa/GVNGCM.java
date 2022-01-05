package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.UQNodes;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

import java.util.BitSet;

// Global Value Numbering, Global Code Motion
public class GVNGCM {
  public static final KeepNode KEEP_ALIVE = new KeepNode();

  // Iterative worklists.
  private final WorkNode _work_dead   = new WorkNode("dead"  );
  private final WorkNode _work_flow   = new WorkNode("flow"  );
  private final WorkNode _work_reduce = new WorkNode("reduce");
  private final WorkNode _work_mono   = new WorkNode("mono"  );
  private final WorkNode _work_grow   = new WorkNode("grow"  );
  private final WorkNode _work_inline = new WorkNode("inline");
  private final WorkNode _work_dom    = new WorkNode("dom"   );
  public boolean on_dead( Node n ) { return _work_dead.on(n); }
  public boolean on_flow( Node n ) { return _work_flow.on(n); }

  static public <N extends Node> N add_work( WorkNode work, N n ) {
    if( n==null || n.is_dead() ) return n;
    work.add(n);
    return n;
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
  public void add_dom(Node n) { add_work(_work_dom,n); }
  public void add_reduce_uses( Node n ) { add_work_uses(_work_reduce,n); }
  // n goes unused
  public void add_unuse( Node n ) {
    if( n._uses._len==0 ) add_dead(n); // might be dead
    else add_reduce(add_flow(n));
  }
  static public void add_work_defs( WorkNode work, Node n ) {
    for( Node def : n._defs )
      if( def != null && def != n )
        add_work(work,def);
  }
  static public void add_work_uses( WorkNode work, Node n ) {
    for( Node use : n._uses )
      if( use != n )
        add_work(work,use);
  }
  public Node add_work_new( Node n ) {
    if( n.is_dead() ) return n;
    add_flow(n);
    add_reduce(n);
    add_mono(n);
    add_grow(n);
    if( n instanceof FunNode )
      _work_inline.add(n);
    return n;
  }

  public Node pop_flow() { return _work_flow.pop(); }

  // Initial state after loading e.g. primitives.
  void init0() {
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  void reset_to_init0() {
    _work_dead  .clear();
    _work_flow  .clear();
    _work_reduce.clear();
    _work_mono  .clear();
    _work_grow  .clear();
    _work_inline.clear();
    _work_dom   .clear();
    ITER_CNT = ITER_CNT_NOOP = 0;
  }
  void flow_clear() { _work_flow.clear(); }

  // Keep a Node reference alive for later.  Strongly asserted as a stack
  public static int push( Node n ) { KEEP_ALIVE.add_def(n); return KEEP_ALIVE._defs._len; }
  // Return the pushed Node
  public static Node pop( int idx ) {
    assert KEEP_ALIVE._defs._len==idx;
    return KEEP_ALIVE.del(idx-1);
  }

  // Record a Node, but do not optimize it for value and ideal calls, as it is
  // mid-construction from the parser.  Any function call with yet-to-be-parsed
  // call sites, and any loop top with an unparsed backedge needs to use this.
  public <N extends Node> N init( N n ) {
    assert n._uses._len==0;     // New to GVN
    n._val = n.value();
    add_work_new(n);
    return n;
  }

  // Apply graph-rewrite rules on new nodes (those with no users and kept alive
  // for the parser).  Return a node registered with GVN that is possibly "more
  // ideal" than what was before.
  public Node xform( Node n ) {
    int idx = push(init(n));
    do_iter();
    return pop(idx);
  }

  // Any time anything is on any worklist we can always conservatively iterate on it.
  // Empties the worklists, attempting to do every possible thing.
  static int ITER_CNT;
  static int ITER_CNT_NOOP;
  void do_iter() {
    while( true ) {
      Node n, m;
      if( false ) ;
      else if( (n=_work_dead  .pop())!=null ) m = n._uses._len == 0 ? n.kill() : null;
      else if( (n=_work_flow  .pop())!=null ) m = n.do_flow  ();
      else if( (n=_work_reduce.pop())!=null ) m = n.do_reduce();
      else if( (n=_work_mono  .pop())!=null ) m = n.do_mono  ();
      else if( (n=_work_grow  .pop())!=null ) m = n.do_grow  ();
      else if( (n=_work_inline.pop())!=null ) m = ((FunNode)n).ideal_inline(false);
      else break;
      ITER_CNT++; assert ITER_CNT < 50000; // Catch infinite ideal-loops
      if( m == null ) ITER_CNT_NOOP++;     // No progress profiling
      else assert m.is_dead() || m.check_vals();
      // VERY EXPENSIVE ASSERT
      //assert Env.START == null || Env.START.more_work(true) == 0; // Initial conditions are correct
    }
  }

  // Top-level iter cleanout.  Empties all queues & aggressively checks
  // no-more-progress.
  private static final VBitSet IDEAL_VISIT = new VBitSet();
  public void iter() {
    while( true ) {
      do_iter();
      // Only a very few nodes can make progress via dominance relations, and
      // these can make progress "very far" in the graph.  So instead of using
      // a neighbors list, we bulk revisit them here.
      boolean progress=false;
      for( int i=0; i<_work_dom.len(); i++ ) {
        Node dom = _work_dom.at(i);
        if( dom.is_dead() ) _work_dom.del(i--);
        else progress |= dom.do_mono()!=null;
      }
      if( !progress ) break;
    };
    // Expensive assert
    assert Env.START.more_work(true)==0;
    IDEAL_VISIT.clear();
    assert !Env.START.more_ideal(IDEAL_VISIT);
  }

  // Clear the dead worklist only
  public void iter_dead() {
    Node n;
    while( (n=_work_dead.pop()) != null )
      if( n._uses._len == 0 )
        n.kill();
  }

  // Did a bulk not-monotonic update.  Forcibly update the entire region at
  // once; restores monotonicity over the whole region when done.
  public void revalive(Node... ns) {
    for( Node n : ns ) {
      if( n == null ) continue;
      Type t = n.value();
      if( t != n._val ) {
        n._val = t;
        add_flow_uses(n);
      }
    }
    for( int i=ns.length-1; i>=0; i-- ) {
      Node n = ns[i];
      if( n==null ) continue;
      TypeMem t = n.live();
      if( t != n._live ) {
        n._live=t;
        add_flow_defs(n);
      }
    }
  }

  // Walk all memory edges, and 'retype' them, probably DOWN (counter to
  // 'iter').  Used when inlining, and the inlined body needs to acknowledge
  // bypasses aliases.  Used during code-clone, to lift the split alias parent
  // up & out.
  private static final WorkNode WORK_RETYPE = new WorkNode("retype");
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
      Type tval = wrk.value();     // Recompute memory value
      if( twrk == tval ) continue; // No change
      wrk._val = tval;             // Progress!!!
      Env.GVN.add_flow_uses(wrk);  // Forwards flow the update
      if( wrk==exit ) continue;    // Stop at end
      if( skip_calls && wrk instanceof MProjNode && wrk.in(0) instanceof CallNode )
        continue;               // Skip the inside of calls

      WORK_RETYPE.add(wrk._uses);
    }
    //assert Env.START.more_work(true)==0;
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
