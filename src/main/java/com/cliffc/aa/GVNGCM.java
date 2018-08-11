package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;
import com.cliffc.aa.util.Ary;

import java.util.Arrays;
import java.util.BitSet;
import java.util.concurrent.ConcurrentHashMap;

// Global Value Numbering, Global Code Motion
public class GVNGCM {
  // Unique dense node-numbering
  private int CNT;
  private BitSet _live = new BitSet();  // Conservative approximation of live; due to loops some things may be marked live, but are dead

  public int uid() { assert CNT < 100000 : "infinite node create loop"; _live.set(CNT);  return CNT++; }

  // Iterative worklist
  private Ary<Node> _work = new Ary<>(new Node[1], 0);
  private BitSet _wrk_bits = new BitSet();

  public void add_work( Node n ) { if( !_wrk_bits.get(n._uid) ) add_work0(n); }
  private <N extends Node> N add_work0( N n ) {
    _work.add(n);               // These need to be visited later
    _wrk_bits.set(n._uid);
    return n;
  }

  // Array of types representing current node types.  Essentially a throw-away
  // temp extra field on Nodes.  It is either bottom-up, conservatively correct
  // or top-down and optimistic.
  private Ary<Type> _ts = new Ary<>(new Type[1],0);

  // Global expressions, to remove redundant Nodes
  private ConcurrentHashMap<Node,Node> _vals = new ConcurrentHashMap<>();

  public String dump( Node n, int max ) { return n.dump(max,this); }
  
  // Initial state after loading e.g. primitives & boot libs.  Record state
  // here, so can reset to here cheaply and parse again.
  public static int _INIT0_CNT;
  private static Node[] _INIT0_NODES;
  void init0() {
    assert _live.get(CNT-1) && !_live.get(CNT) && _work._len==0 && _wrk_bits.isEmpty() && _ts._len==CNT;
    _INIT0_CNT=CNT;
    _INIT0_NODES = _vals.keySet().toArray(new Node[0]);
    for( Node n : _INIT0_NODES ) assert !n.is_dead();
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  void reset_to_init0() {
    assert _work._len==0 && _wrk_bits.isEmpty();
    CNT = _INIT0_CNT;
    _live.clear();  _live.set(0,_INIT0_CNT);
    _ts.set_len(_INIT0_CNT);
    _vals.clear();
    for( Node n : _INIT0_NODES ) {
      assert !n.is_dead();
      _vals.put(n,n);
      for( int i=0; i<n._uses._len; i++ )
        if( n._uses.at(i)._uid >= CNT )
          n._uses.del(i--);
    }
  }

  private boolean _opt=false;
  public Type type( Node n ) {
    Type t = n._uid < _ts._len ? _ts._es[n._uid] : null;
    if( t != null ) return t;
    t = n.all_type();           // If no type yet, defaults to the pessimistic type
    if( _opt ) t = t.dual();    // If running optimistic GCP, want the dual instead
    return _ts.setX(n._uid,t);
  }
  private void setype( Node n, Type t ) {
    assert t != null;
    _ts.setX(n._uid,t);
  }
  // Make globally shared common ConNode for this type.
  public Node con( Type t ) {
    Node con = new ConNode<>(t);
    Node con2 = _vals.get(con);
    if( con2 != null ) { kill0(con); return con2; } // TODO: con goes dead, should be recycled
    setype(con,t);
    _vals.put(con,con);
    return con;
  }

  // Record a Node, but do not optimize it for value and ideal calls, as it is
  // mid-construction from the parser.  Any function call with yet-to-be-parsed
  // call sites, and any loop top with an unparsed backedge needs to use this.
  public <N extends Node> N init( N n ) {
    assert n._uses._len==0;
    return init0(n);
  }
  <N extends Node> N init0( N n ) {
    setype(n,n.all_type());
    _vals.put(n,n);
    return add_work0(n);
  }

  // Add a new def to 'n', changing its hash - so rehash it
  public void add_def( Node n, Node def ) {
    Node x = _vals.remove(n);
    assert x == n;
    n.add_def(def);
    _vals.put(n,n);
    add_work(n);
  }

  // True if in _ts and _vals, false otherwise
  public boolean touched( Node n ) { return n._uid < _ts._len && _ts._es[n._uid]!=null; }
  
  // Remove from GVN structures.  Used rarely for whole-merge changes
  public void unreg( Node n ) { assert !check_new(n); unreg0(n); }
  private Node unreg0( Node n ) {
    _ts.set(n._uid,null);       // Remove from type system
    _vals.remove(n);            // Remove from GVN
    // TODO: Remove from worklist also
    return n;
  }
  
  // Used rarely for whole-merge changes
  public Node rereg( Node n ) {
    assert !check_opt(n);
    return init0(n);
  }

  // Hack an edge, updating GVN as needed
  public void set_def_reg(Node n, int idx, Node def) {
    _vals.remove(n);            // Remove from GVN
    n.set_def(idx,def,this);    // Hack edge
    assert !check_gvn(n,false); // Check not in GVN table after hack
    _vals.put(n,n);             // Back in GVN table
    add_work(n);
  }
  
  // Node new to GVN and unregistered, or old and registered
  private boolean check_new(Node n) {
    if( check_opt(n) ) return false; // Not new
    assert n._uses._len==0;          // New, so no uses
    return true;
  }
  // Node is in the type table and GVN hash table
  private boolean check_opt(Node n) {
    if( touched(n) ) {          // First & only test: in type table or not
      assert (n instanceof ScopeNode) || _wrk_bits.get(n._uid)  || check_gvn(n,true); // Check also in GVN table
      return true;              // Yes in both type table and GVN table
    }
    assert !check_gvn(n,false); // Check also not in GVN table
    return false;               // Node not in tables
  }

  private boolean check_gvn( Node n, boolean expect ) {
    Node x = _vals.get(n), old=null;
    if( x == n ) {              // Found in table
      assert expect;            // Expected to be found
      return true;              // Definitely in table
    }
    boolean found = false;
    for( Node o : _vals.keySet() ) if( (old=o)._uid == n._uid ) { found=true; break; }
    assert found == expect || _wrk_bits.get(n._uid) : "Found but not expected: "+old.toString(); // Expected in table or on worklist
    return false;               // Not in table
  }

  // Apply graph-rewrite rules on new nodes (those with no users and kept alive
  // for the parser).  Return a node registered with GVN that is possibly "more
  // ideal" than what was before.
  public Node xform( Node n ) {
    assert check_new(n);

    // Try generic graph reshaping, looping till no-progress.
    int cnt=0;  Node x;         // Progress bit
    while( (x = n.ideal(this)) != null ) {
      if( x != n ) {            // Different return, so delete original dead node
        x._uses.add(x);         // Hook X to prevent accidental deletion
        kill_new(n); // n was new, replaced so immediately recycle n and dead subgraph
        n = x._uses.del(x._uses.find(x)); // Remove hook, keep better n
      }
      if( !check_new(n) ) return n; // If the replacement is old, no need to re-ideal
      cnt++; assert cnt < 1000;     // Catch infinite ideal-loops
    }
    // Compute a type for n
    Type t = n.value(this);              // Get best type
    // Replace with a constant, if possible
    if( t.may_be_con() && !(n instanceof ConNode) )
      { kill_new(n); return con(t); }
    // Global Value Numbering
    x = _vals.putIfAbsent(n,n);
    if( x != null ) { kill_new(n); return x; }
    // Record type for n; n is "in the system" now
    setype(n,t);                         // Set it in
    // TODO: If x is a TypeNode, capture any more-precise type permanently into Node
    return n;
  }
  
  // Recursively kill off a new dead node, which might make lots of other nodes
  // go dead.  Since its new, no need to remove from GVN system.  
  public void kill_new( Node n ) { assert check_new(n);  kill0(n); }
  // Recursively kill off a dead node, which might make lots of other nodes go dead
  public void kill( Node n ) {  kill0(unreg0(n)); }
  // Version for never-GVN'd; common for e.g. constants to die early or
  // RootNode, and some other make-and-toss Nodes.
  void kill0( Node n ) {
    assert n._uses._len==0;
    for( int i=0; i<n._defs._len; i++ )
      n.set_def(i,null,this);   // Recursively destroy dead nodes
    n.set_dead();               // n is officially dead now
    _live.clear(n._uid);
    if( n._uid==CNT-1 ) {       // Roll back unused node indices
      while( !_live.get(CNT-1) ) CNT--;
    }
  }
  
  private void xform_old( Node old ) {
    Node nnn = xform_old0(old);
    if( nnn==null ) return;
    if( nnn == old ) {          // Progress, but not replacement
      for( Node use : old._uses ) add_work(use);
      add_work(old);            // Re-run old, until no progress
      return;
    }
    if( check_new(nnn) ) {      // If new, replace back in GVN
      setype(nnn,nnn.value(this));// Can compute a better value
      _vals.put(nnn,nnn);
      add_work0(nnn);
    }
    if( !old.is_dead() ) { // if old is being replaced, it got removed from GVN table and types table.
      assert !check_opt(old);
      subsume(old,nnn);
    }
  }
  /** Look for a better version of 'n'.  Can change n's defs via the ideal()
   *  call, including making new nodes.  Can replace 'n' wholly, with n's uses
   *  now pointing at the replacement.
   *  @param n Node to be idealized; already in GVN
   *  @return null for no-change, or a better version of n, already in GVN */
  private Node xform_old0( Node n ) {
    assert touched(n);         // Node is in type tables, but might be already out of GVN
    _vals.remove(n);           // Remove before modifying edges (and thus hash)
    Type oldt = type(n);       // Get old type
    _ts._es[n._uid] = null;    // Remove from types
    assert !check_opt(n);      // Not in system now
    // Try generic graph reshaping
    Node y = n.ideal(this);
    if( y != null && y != n ) return y;  // Progress with some new node
    if( y != null && y.is_dead() ) return null;
    // Either no-progress, or progress and need to re-insert n back into system
    Type t = n.value(this);     // Get best type
    assert t.isa(oldt);         // Types only improve
    // Replace with a constant, if possible
    if( t.may_be_con() && !(n instanceof ConNode) )
      return con(t);            // Constant replacement
    // Global Value Numbering
    Node z = _vals.putIfAbsent(n,n);
    if( z != null ) return z;
    // Record type for n; n is "in the system" now
    setype(n,t);                // Set it in
    // TODO: If x is a TypeNode, capture any more-precise type permanently into Node
    return oldt == t && y==null ? null : n; // Progress if types improved
  }

  // Complete replacement; point uses to x.  The goal is to completely replace
  // 'old'.
  public void subsume( Node old, Node nnn ) {
    while( old._uses._len > 0 ) {
      Node u = old._uses.del(0);  // Old use
      _vals.remove(u); // Use is about to change edges; remove from type table
      u._defs.set(u._defs.find(old),nnn); // was old now nnn
      nnn._uses.add(u);
      add_work(u);            // And put on worklist, to get re-inserted
    }
    nnn._uses.add(nnn);       // Self-hook, to prevent accidental deletion
    kill(old);                // Delete the old n, and anything it uses
    nnn._uses.del(nnn._uses.find(nnn)); // Remove self-hook
  }

  // Once the program is complete, any time anything is on the worklist we can
  // always conservatively iterate on it.
  void iter() {
    // As a modest debugging convenience, avoid inlining (which blows up the
    // graph) until other optimizations are done.  Gather the possible inline
    // requests and set them aside until the main list is empty, then work down
    // the inline list.
    Ary<Node> funs = new Ary<>(new Node[1], 0);
    BitSet fun_bits = new BitSet();
    boolean work;
    while( (work=_work._len > 0) || funs._len > 0 ) {
      Node n = (work ? _work : funs).pop(); // Pull from main worklist before functions
      (work ? _wrk_bits : fun_bits).clear(n._uid);
      if( n.is_dead() ) continue;
      if( n instanceof ScopeNode || n instanceof TmpNode ) continue; // These are killed when parsing exists lexical scope
      if( n._uses._len==0 ) { kill(n); continue; }
      if( _work._len > 0 && n instanceof FunNode && n.is_copy(this,-1) == null ) {
        // Stall FunNodes, which may inline, until the main list goes empty
        if( !fun_bits.get(n._uid ) ) { funs.add(n); fun_bits.set(n._uid); }
      } else {
        xform_old(n);
      }
    }
  }

  // Global Optimistic Constant Propagation.
  void gcp(ScopeNode start) {
    assert _work._len==0;
    assert _wrk_bits.isEmpty();
    Ary<Node> nodes = new Ary<>(new Node[1],0);
    // Set all types to null, indicating no value/never visited.
    Arrays.fill(_ts._es,_INIT0_CNT,_ts._len,null);
    _opt = true;                // Lazily fill with best value
    // Prime the worklist
    nodes.setX(start._uid,start);
    _ts.setX(start._uid,start.all_type());
    for( Node use : start._uses ) add_work(use); // Users use progress
    // Repeat, if we remove some ambiguous choices, and keep falling until the
    // graph stabilizes without ambiguity.
    while( _work._len > 0 ) {
      // Analysis phase.
      // Work down list until all reachable nodes types quit falling
      while( _work._len > 0 ) {
        Node n = _work.pop();
        _wrk_bits.clear(n._uid);
        assert !n.is_dead();
        nodes.setX(n._uid,n);     // Record back-ptr to Node
        boolean never_seen = _ts._es[n._uid]==null;
        Type ot = type(n);        // Old type
        Type nt = n.value(this);  // New type
        assert ot.isa(nt);        // Types only fall monotonically
        if( ot != nt || never_seen ) // Progress
          _ts.setX(n._uid,nt);    // Record progress
        for( Node use : n._uses ) {
          if( _ts._es[use._uid]==null || // Never typed
              (ot != nt && use.all_type() != type(use))) // If not already at bottom
            if( use != n ) add_work(use); // Re-run users to check for progress
          // When new control paths appear on Regions, the Region stays the
          // same type (Ctrl) but the Phis must merge new values.
          if( use instanceof RegionNode )
            for( Node phi : use._uses ) if( phi != n ) add_work(phi);
        }
      }
      _opt = false;               // Back to pessimistic behavior on new nodes
  
      // Optimization phase 1: Remove ambiguity
      for( int i=_INIT0_CNT; i<_ts._len; i++ ) {
        Node n = nodes.atX(i);
        if( n instanceof CallNode && n.in(1) instanceof UnresolvedNode ) {
          Node fun = ((UnresolvedNode)n.in(1)).resolve(this,(CallNode)n);
          if( fun != null ) {
            set_def_reg(n, 1, fun);
            add_work(n); // Go again- values will continue to fall in the lattice
          }
        }
      }
    }
    
    // Optimization phase 2.
    // Record in any improved types; replace with constants if possible.
    for( int i=_INIT0_CNT; i<_ts._len; i++ ) {
      Type t = _ts._es[i];
      if( t==null ) continue;   // Never reached?
      Node n = nodes.atX(i);
      if( n != null && t.may_be_con() && !(n instanceof ConNode) )
        throw AA.unimpl();
      if( !(t instanceof TypeErr) && n instanceof CastNode ) { // TODO: Fold into CastNode.ideal
        assert t.isa(((CastNode)n)._t);
        if( t != (((CastNode)n)._t)) {
          unreg(n);
          Node cast = xform_old0(rereg(new CastNode(n.in(0), n.in(1), t)));
          subsume(n, nodes.setX(cast._uid, cast));
        }
      }
      //if( n instanceof FunNode ) 
      //  throw AA.unimpl();
    }

    // Re-check all ideal calls now that types have been maximally lifted
    for( int i=_INIT0_CNT; i<_ts._len; i++ )
      if( nodes.atX(i) != null )
        add_work(nodes.at(i));
    iter();
  }
}
