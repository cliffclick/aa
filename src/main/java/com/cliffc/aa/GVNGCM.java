package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.UQNodes;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;

// Global Value Numbering, Global Code Motion
public class GVNGCM {
  // Iterative worklists.
  private final WorkNode _work_dead   = new WorkNode("dead"  );
  private final WorkNode _work_flow   = new WorkNode("flow"  );
  private final WorkNode _work_reduce = new WorkNode("reduce");
  private final WorkNode _work_mono   = new WorkNode("mono"  );
  private final WorkNode _work_grow   = new WorkNode("grow"  );
  private final WorkNode _work_inline = new WorkNode("inline");
  public boolean on_dead  ( Node n ) { return _work_dead  .on(n); }
  public boolean on_flow  ( Node n ) { return _work_flow  .on(n); }
  public boolean on_reduce( Node n ) { return _work_reduce.on(n); }
  public boolean on_mono  ( Node n ) { return _work_mono  .on(n); }
  public boolean on_grow  ( Node n ) { return _work_grow  .on(n); }
  public boolean on_inline( Node n ) { return _work_inline.on(n); }

  static public <N extends Node> N add_work( WorkNode work, N n ) {
    if( n==null || n.isDead() || n.isPrim() ) return n;
    work.add(n);
    return n;
  }
  public void add_dead  ( Node n ) { add_work(_work_dead, n); }
  public <N extends Node> N add_reduce( N n ) { return add_work(_work_reduce,n); }
  public <N extends Node> N add_flow  ( N n ) { return add_work(_work_flow  ,n); }
  public <N extends Node> N add_mono  ( N n ) { return add_work(_work_mono  ,n); }
  public <N extends Node> N add_flow_reduce( N n ) { return add_flow(add_reduce(n)); }

  public void add_grow  ( Node n ) { add_work(_work_grow  ,n); }
  public void add_inline( FunNode n ) { add_work(_work_inline, n); }
  public void add_flow_defs  ( Node n ) { add_work_defs(_work_flow,n); }
  public void add_flow_uses  ( Node n ) { add_work_uses(_work_flow,n); }
  public void add_flow( UQNodes deps ) { if( deps != null ) for( Node dep : deps.values() ) add_flow(dep); }
  public void add_reduce_uses( Node n ) { add_work_uses(_work_reduce,n); }
  // n goes unused
  public void add_unuse( Node n ) {
    if( n.nUses()==0 ) add_dead(n); // might be dead
    else add_reduce(add_flow(n));
  }
  public static void add_work_defs( WorkNode work, Node n ) {
    for( Node def : n.defs() )
      if( def != null && def != n )
        add_work(work,def);
  }
  public static void add_work_uses( WorkNode work, Node n ) {
    for( Node use : n.uses() )
      if( use != n )
        add_work(work,use);
  }
  public Node add_work_new( Node n ) {
    if( n.isDead() ) return n;
    add_flow(n);
    add_reduce(n);
    add_mono(n);
    add_grow(n);
    if( n instanceof FunNode )
      _work_inline.add(n);
    return n;
  }
  public <N extends Node> void add_flow( Ary<N> ary ) { for( Node n : ary ) add_flow(n); }

  public Node pop_flow() { return _work_flow.pop(); }
  public int flow_len() { return _work_flow.len(); }

  // Initial state after loading e.g. primitives.
  void init0() {
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  public void reset_to_init0() {
    _work_dead  .clear();  _work_dead  .setSeed(AA.RSEED);
    _work_flow  .clear();  _work_flow  .setSeed(AA.RSEED);
    _work_reduce.clear();  _work_reduce.setSeed(AA.RSEED);
    _work_mono  .clear();  _work_mono  .setSeed(AA.RSEED);
    _work_grow  .clear();  _work_grow  .setSeed(AA.RSEED);
    _work_inline.clear();  _work_inline.setSeed(AA.RSEED);
    ITER_CNT = ITER_CNT_NOOP = 0;
  }
  boolean work_is_clear() { return _work_flow.isEmpty() && _work_dead.isEmpty() && _work_reduce.isEmpty(); }
  public void work_clear() {
    _work_flow.clear();
    _work_dead.clear();
    _work_reduce.clear();
  }

  // Apply graph-rewrite rules on new nodes (those with no users and kept alive
  // for the parser).  Return a node registered with GVN that is possibly "more
  // ideal" than what was before.
  public Node xform( Node n ) {
    //int idx = push(init(n));
    //iter();
    //// Last KEEP use is going away; this Node should rapidly be used by an actual
    //// Node, and thus be able to compute liveness.
    //return add_flow(pop(idx));
    throw AA.TODO();
  }

  // During start-up, ~2000 total iterations, something like 95% of which are
  // no-ops.  Also, about 500 nodes for primitives, and each hits flow, reduce,
  // mono and grow worklists (so 4 times) for no-progress.
  static int ITER_CNT;
  static int ITER_CNT_NOOP;

  // Top-level iter clean-out.  Does everything it can, empties all queues and
  // aggressively checks no-more-progress.
  public void iter() {
    int cnt = ITER_CNT;
    assert !NodeUtil.leak();
    assert NodeUtil.more_work(Env.ROOT) == 0; // Initial conditions are correct
    //assert NodeUtil.no_more_ideal(Env.ROOT);
    while( true ) {
      cnt++; assert cnt < 10000; // Catch infinite ideal-loops
      Node n, m;
      if( false ) ;
      else if( (n=_work_dead  .pop())!=null ) m = n.nUses() == 0 ? n.kill() : null;
      else if( (n=_work_flow  .pop())!=null ) m = n.do_flow  ();
      else if( (n=_work_reduce.pop())!=null ) m = n.do_reduce();
      else if( (n=_work_mono  .pop())!=null ) m = n.do_mono  ();
      else if( (n=_work_grow  .pop())!=null ) m = n.do_grow  ();
      else if( (n=_work_inline.pop())!=null ) m = ((FunNode)n).ideal_inline(false);
      else break;
      if( m == null ) ITER_CNT_NOOP++;     // No progress profiling
      else n.deps_work_clear();            // Progress; deps on worklist
      //assert NodeUtil.more_work(Env.ROOT) == 0;
      //assert NodeUtil.no_more_ideal(Env.ROOT);
      assert !NodeUtil.leak();
    }
    assert NodeUtil.more_work(Env.ROOT)==0;
    //assert NodeUtil.no_more_ideal(Env.ROOT);
    assert !NodeUtil.leak();
    ITER_CNT=cnt;
  }

  // Did a bulk not-monotonic update.  Forcibly update the entire region at
  // once; restores monotonicity over the whole region when done.
  public void revalive(Node... ns) {
    for( Node n : ns ) {
      if( n == null || n.isDead() ) continue;
      Type t = n.value();
      if( t != n._val ) {
        n._val = t;
        add_flow_uses(n);
      }
    }
    for( int i=ns.length-1; i>=0; i-- ) {
      Node n = ns[i];
      if( n==null || n.isDead() ) continue;
      Type t = n.live();
      if( t != n._live ) {
        n._live=t;
        add_flow_defs(n);
      }
    }
  }
}
