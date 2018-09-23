package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
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

  // Code-expanding worklist, lower priority work
  private Ary<Node> _work2 = new Ary<>(new Node[1], 0);
  private BitSet _wrk2_bits = new BitSet();
  public void add_work2( Node n ) {
    if( !_wrk2_bits.get(n._uid) ) {
      _work2.add(n);
      _wrk2_bits.set(n._uid);
    }
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
    while( _work._len > 0 ) {   // Can be a few leftover dead bits...
      Node n = _work.pop();     // from top-level parse killing result...
      _wrk_bits.clear(n._uid);  // after getting type to return
      assert n.is_dead();
    }
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

  public boolean _opt=false;
  public Type type( Node n ) {
    Type t = n._uid < _ts._len ? _ts._es[n._uid] : null;
    if( t != null ) return t;
    t = n.all_type();       // If no type yet, defaults to the pessimistic type
    return _ts.setX(n._uid,t);
  }
  private void setype( Node n, Type t ) {
    assert t != null;
    _ts.setX(n._uid,t);
  }
  // Make globally shared common ConNode for this type.
  public ConNode con( Type t ) {
    ConNode con = new ConNode<>(t);
    Node con2 = _vals.get(con);
    if( con2 != null ) { kill0(con); return (ConNode)con2; } // TODO: con goes dead, should be recycled
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
    assert x == n || (x==null && _wrk_bits.get(n._uid));
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
  public Node rereg( Node n, Type oldt ) {
    assert !check_opt(n);
    setype(n,oldt);
    _vals.put(n,n);
    return add_work0(n);
  }

  // Hack an edge, updating GVN as needed
  public void set_def_reg(Node n, int idx, Node def) {
    _vals.remove(n);            // Remove from GVN
    n.set_def(idx,def,this);    // Hack edge
    if( n.is_dead() ) return;
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
    int cnt=0;  Node x;        // Progress bit
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
      assert _ts.at(nnn._uid)==nnn.value(this);
      //setype(nnn,nnn.value(this));// Can compute a better value
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
    if( t.may_be_con() && !(n instanceof ConNode) && !(n instanceof ErrNode) )
      return con(t);            // Constant replacement
    // Global Value Numbering
    Node z = _vals.putIfAbsent(n,n);
    if( z != null ) return z;
    // Record type for n; n is "in the system" now
    setype(n,t);                // Set it in
    // TODO: If x is a TypeNode, capture any more-precise type permanently into Node
    return oldt == t && y==null ? null : n; // Progress if types improved
  }

  // Complete replacement; point uses to 'nnn'.  The goal is to completely replace 'old'.
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
  public boolean _small_work;
  void iter() {
    // As a modest debugging convenience, avoid inlining (which blows up the
    // graph) until other optimizations are done.  Gather the possible inline
    // requests and set them aside until the main list is empty, then work down
    // the inline list.
    while( (_small_work=_work._len > 0) || _work2._len > 0 ) {
      Node n = (_small_work ? _work : _work2).pop(); // Pull from main worklist before functions
      (_small_work ? _wrk_bits : _wrk2_bits).clear(n._uid);
      if( n.is_dead() ) continue;
      if( n._uses._len==0 ) kill(n);
      else xform_old(n);
    }
  }

  // Global Optimistic Constant Propagation.
  void gcp(ScopeNode start, ScopeNode end) {
    assert _work._len==0;
    assert _wrk_bits.isEmpty();
    Ary<Node> calls = new Ary<>(new Node[1],0);
    // Set all types to all_type().dual()
    Arrays.fill(_ts._es,_INIT0_CNT,_ts._len,null);
    walk_initype( end );
    for( Node use : start._uses ) walk_initype( use ); // Grab all constants
    // Prime worklist
    add_work(end);
    
    _opt = true;                // Lazily fill with best value
    // Repeat, if we remove some ambiguous choices, and keep falling until the
    // graph stabilizes without ambiguity.
    while( _work._len > 0 ) {
      // Analysis phase.
      // Work down list until all reachable nodes types quit falling
      while( _work._len > 0 ) {
        Node n = _work.pop();
        _wrk_bits.clear(n._uid);
        assert !n.is_dead();
        if( n._uid < _INIT0_CNT ) continue; // Ignore primitives (type is unchanged and conservative)
        if( n instanceof CallNode && n.in(1) instanceof UnresolvedNode && calls.find(n)== -1 )
          calls.add(n);          // Track ambiguous calls
        Type ot = type(n);       // Old type
        Type nt = n.value(this); // New type
        assert ot.isa(nt);       // Types only fall monotonically
        if( ot != nt )           // Progress
          _ts.setX(n._uid,nt);   // Record progress
        for( Node use : n._uses ) {
          if( type(use) == Type.ANY || // Not yet typed
              (ot != nt && use.all_type() != type(use))) // If not already at bottom
            if( use != n ) add_work(use); // Re-run users to check for progress
          // When new control paths appear on Regions, the Region stays the
          // same type (Ctrl) but the Phis must merge new values.
          if( use instanceof RegionNode )
            for( Node phi : use._uses ) if( phi != n ) add_work(phi);
        }
      }

      // Remove ambiguity after worklist runs dry
      for( int i=0; i<calls.len(); i++ ) {
        Node call = calls.at(i);
        if( !call.is_dead() ) {
          Node fun = ((UnresolvedNode)call.in(1)).resolve(this,(CallNode)call);
          if( fun != null ) {
            set_def_reg(call, 1, fun);
            calls.del(i--); // Remove from worklist
          }
        }
      }
    }

    _opt = false;               // Back to pessimistic behavior on new nodes

    // Revisit the entire reachable program, as ideal calls may do something
    // with the maximally lifted types.
    Node rez = end.in(end._defs._len-2);
    FunNode frez = rez instanceof EpilogNode ? ((EpilogNode)rez).fun() : null;
    /* TODO: Cliff Notes; see ParmNode & FunNode value calls for slot#1.  If
       some Epilog is being kept as a plain F-P and not called then the FunNode
       needs to be kept live - even without callers.  How do i detect a F-P
       usage where the F-P is stored in a data structure, and called later?
       All such usages should be matchable to call sites.  But in any case, F-P
       taken implies some unknown callers...  currently returning a F-P that is
       not otherwise called, looks like the RPC stays at the "never called"
       stage.  Once in iter(), again acts like "being called".
     */
    walk_opt(rez,start,frez);
  }

  // Forward reachable walk, setting all_type.dual (except Start) and priming
  // the worklist for nodes that are not above centerline.
  private void walk_initype( Node n ) {
    if( _ts.atX(n._uid) != null ) return; // Been there, done that
    Type t = n.all_type();
    if( !t.above_center() && !(n instanceof ErrNode) && !(n instanceof ConNode) )
      t = t.dual();             // Start above-center and fall
    if( !t.above_center() || n instanceof ConNode || n instanceof ErrNode ) // Constants and errors act as-if they started high and fell to the constant value ...
      for( Node use : n._uses ) add_work(use); // ...by adding users
    setype(n,t);
    // Walk forward reachable graph
    for( Node use : n._uses ) walk_initype(use);
  }
  
  // GCP optimizations on the live subgraph
  private void walk_opt( Node n, Node start, FunNode frez ) {
    assert !n.is_dead();
    if( _wrk_bits.get(n._uid) ) return; // Been there, done that
    if( n==start ) return;              // Top-level scope
    add_work(n);                        // Only walk once
    // Functions have no more unknown callers
    if( n instanceof FunNode && n._uid >= _INIT0_CNT ) {
      FunNode fun = (FunNode)n;
      if( !fun._tf.is_forward_ref() && // No forward ref (error at this point)
          !fun._busted_call &&         // No broken calls (error at this point)
          !fun._all_callers_known &&   // Not already flagged as all-calls-known
          fun != frez) {               // Not being returned as top-level result
        fun.all_callers_known();
        set_def_reg(fun,1,con(Type.XCTRL));
      }
    }
    
    // Walk reachable graph
    for( Node def : n._defs )
      if( def != null &&
          !(n instanceof RegionNode && type(def)== Type.XCTRL) )
        walk_opt(def,start,frez);
  }

}
