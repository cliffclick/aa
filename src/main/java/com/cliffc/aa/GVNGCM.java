package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import org.jetbrains.annotations.NotNull;

import java.util.Set;
import java.util.BitSet;
import java.util.concurrent.ConcurrentHashMap;

// Global Value Numbering, Global Code Motion
public class GVNGCM {
  // Unique dense node-numbering
  private int CNT;
  private final BitSet _live = new BitSet();  // Conservative approximation of live; due to loops some things may be marked live, but are dead

  public int uid() { assert CNT < 100000 : "infinite node create loop"; _live.set(CNT);  return CNT++; }

  public int _opt_mode;         // 0 - Parse (discovery), 1 - iter (lifting), 2 - gcp/opto (falling)

  // Iterative worklist
  private final Ary<Node> _work = new Ary<>(new Node[1], 0);
  private final BitSet _wrk_bits = new BitSet();

  public Node add_work( Node n ) { if( !_wrk_bits.get(n._uid) ) add_work0(n); return n;}
  private <N extends Node> N add_work0( N n ) {
    _work.add(n);               // These need to be visited later
    _wrk_bits.set(n._uid);
    return n;
  }
  public boolean on_work( Node n ) { return _wrk_bits.get(n._uid); }
  // Add all uses as well
  public void add_work_uses( Node n ) {
    for( Node use : n._uses )  add_work(use);
    // Add self at the end, so the work loops pull it off again.
    if( touched(n)  ) add_work(n); // Do not re-add if mid-ideal-call.
  }
  // All defs on worklist - liveness flows uphill
  public void add_work_defs( Node n ) {
    for( Node def : n._defs ) // Put defs on worklist... liveness flows uphill
      if( def != null && def != n )
        add_work(def);
  }

  // A second worklist, for code-expanding and thus lower priority work.
  // Inlining happens off this worklist, once the main worklist runs dry.
  private final Ary<Node> _work2 = new Ary<>(new Node[1], 0);
  private final VBitSet _wrk2_bits = new VBitSet();
  public void add_work2( Node n ) {
    if( !_wrk2_bits.tset(n._uid) )
      _work2.add(n);
  }

  // Array of types representing current node types.  Essentially a throw-away
  // temp extra field on Nodes.  It is either bottom-up, conservatively correct
  // or top-down and optimistic.
  private final Ary<Type> _ts = new Ary<>(new Type[1],0);

  // Global expressions, to remove redundant Nodes
  private final ConcurrentHashMap<Node,Node> _vals = new ConcurrentHashMap<>();
  Set<Node> valsKeySet() { return _vals.keySet(); }

  // Initial state after loading e.g. primitives.
  public static int _INIT0_CNT;
  void init0() {
    assert _live.get(CNT-1) && !_live.get(CNT) && _work._len==0 && _wrk_bits.isEmpty() && _ts._len==CNT;
    _INIT0_CNT=CNT;
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  void reset_to_init0() {
    _work .clear(); _wrk_bits .clear();
    _work2.clear(); _wrk2_bits.clear();
    _opt_mode = 0;
    CNT = 0;
    _live.clear();
    _ts.clear();
    _vals.clear();
  }

  public Type type( Node n ) {
    Type t = _ts.atX(n._uid);
    return t==null ? Type.ALL : t;
  }
  public Type raw_type( int uid ) { return _ts.atX(uid); }
  public void setype( Node n, Type t ) {
    assert t==t.simple_ptr(); // No null, no complex pointers
    _ts.setX(n._uid,t);
  }
  // Utility: remove old from type table, return new
  public Node untype( Node old, Node nnn ) { _ts.clear(old._uid); return nnn; }
  // Return the prior self_type during the value() call, without installing a
  // new type.
  public Type self_type( Node n ) {
    return n._uid < _ts._len ? _ts._es[n._uid] : Type.ALL;
  }
  // Make globally shared common ConNode for this type.
  public @NotNull ConNode con( Type t ) {
    // Check for a function constant, and return the globally shared common
    // FunPtrNode instead.  This only works for FunPtrs with no closures.
    assert !(t instanceof TypeFunPtr && t.is_con()); // Does not work for function constants
    ConNode con = new ConNode<>(t);
    Node con2 = _vals.get(con);
    if( con2 != null ) {           // Found a prior constant
      kill0(con);                  // Kill the just-made one
      con2._live = (TypeMem)con2._live.meet(TypeMem.EMPTY);  // Prior constant is now alive; might have been either dead or alive before
      return (ConNode)con2;
    }
    con._live = TypeMem.EMPTY;  // Alive, but demands no memory
    setype(con,t);
    _vals.put(con,con);
    add_work(con);
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
    setype(n,Type.ALL);
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
  public void remove( Node n, int idx ) {
    Node x = _vals.remove(n);
    assert x == n || (x==null && _wrk_bits.get(n._uid));
    n.remove(idx,this);
    _vals.put(n,n);
    add_work(n);
  }

  // True if in _ts and _vals, false otherwise
  public boolean touched( Node n ) { return _ts.atX(n._uid)!=null; }

  // Remove from GVN structures.  Used rarely for whole-merge changes
  public Type unreg( Node n ) { assert check_opt(n); return unreg0(n); }
  private Type unreg0( Node n ) {
    Type t = n._uid < _ts._len ? _ts.set(n._uid,null) : null; // Remove from type system
    _vals.remove(n);            // Remove from GVN
    return t;
  }

  // Used rarely for whole-merge changes
  public void rereg( Node n, Type oldt ) {
    assert !check_opt(n);
    setype(n,oldt);
    _vals.putIfAbsent(n,n);     // 'n' will not go back if it hits a prior
    add_work_uses(n);
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
  public void remove_reg(Node n, int idx) {
    _vals.remove(n);            // Remove from GVN
    n.remove(idx,this);         // Hack edge
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
  public boolean check_out( Node n) { return _vals.get(n)!=n; }

  // Apply graph-rewrite rules on new nodes (those with no users and kept alive
  // for the parser).  Return a node registered with GVN that is possibly "more
  // ideal" than what was before.
  public Node xform( Node n ) {
    assert check_new(n);

    // Try generic graph reshaping, looping till no-progress.
    int cnt=0;                  // Progress bit
    while( true ) {
      // Compute a type for n
      Type t = n.value(this);   // Get best type
      // Replace with a constant, if possible
      if( replace_con(t,n) )
        { kill_new(n); return con(t); }
      setype(n,t);              // Set it in for ideal
      Node x = n.ideal(this,0);
      if( x == null ) break;
      if( x != n ) {          // Different return, so delete original dead node
        x.keep();             // Keep alive during deletion of n
        kill(n);              // replace so immediately recycle n and dead subgraph
        n = x.unhook();       // Remove keep-alive
        if( !check_new(x) ) return x; // If the replacement is old, no need to re-ideal
        add_work_defs(n);       // Force live-ness rechecking
      }
      untype(n,null);           // Pull out for invariants on next iteration
      cnt++; assert cnt < 100;  // Catch infinite ideal-loops
    }
    // Global Value Numbering; n is "in the system" now
    Node x = _vals.putIfAbsent(n,n);
    if( x != null ) { untype(n,null); kill_new(n); return x; }
    return add_work(n);
  }

  // Recursively kill off a new dead node, which might make lots of other nodes
  // go dead.  Since its new, no need to remove from GVN system.
  public void kill_new( Node n ) { assert check_new(n);  kill0(n); }
  // Recursively kill off a dead node, which might make lots of other nodes go dead
  public void kill( Node n ) {  unreg0(n); kill0(n); }
  // Version for never-GVN'd; common for e.g. constants to die early or
  // RootNode, and some other make-and-toss Nodes.
  private void kill0( Node n ) {
    assert n._uses._len==0 && n._keep==0;
    for( int i=0; i<n._defs._len; i++ )
      n.set_def(i,null,this);   // Recursively destroy dead nodes
    n.set_dead();               // n is officially dead now
    _live.clear(n._uid);
    _wrk_bits.clear(n._uid);
    _wrk2_bits.clear(n._uid);
    if( n._uid==CNT-1 ) {       // Roll back unused node indices
      while( !_live.get(CNT-1) ) CNT--;
    }
  }

  // Replace with a ConNode iff
  // - Not already a ConNode AND
  // - Not an ErrNode AND
  // - Type.is_con()
  private boolean replace_con(Type t, Node n) {
    if( n._keep >0 || n instanceof ConNode || n instanceof ErrNode )
      return false; // Already a constant, or never touch an ErrNode
    if( !t.is_con() ) {
      if( t instanceof TypeFunPtr && !(n instanceof FunPtrNode) )
        return ((TypeFunPtr)t).can_be_fpnode();
      return false;
    }
    // Parm is in-error; do not remove the error.
    if( n instanceof ParmNode && n.err(this) != null )
      return false;
    // Constant argument to call: keep for call resolution.
    // Call can always inline to fold constant.
    if( n instanceof ProjNode && n.in(0) instanceof CallNode )
      return false;
    return true; // Replace with a ConNode
  }

  public void xform_old( Node old, int level ) {
    Node nnn = xform_old0(old,level);
    if( nnn==null ) return;     // No progress
    assert (level&1)==0;        // No changes during asserts
    // Progress, so changes to the users which might change live-use-ness.
    for( Node use : old._uses )
      if( use.input_value_changes_live() )
        add_work_defs(use);
    // Progress, but not replacement
    if( nnn == old ) {
      // All users on worklist
      for( Node use : old._uses ) {
        add_work(use);
        if( use instanceof RegionNode ) // Region users need to recheck PhiNode
          add_work_uses(use);
        if( use instanceof ParmNode && ((ParmNode)use)._idx==-2 )
          add_work(use.in(0));  // Recheck function inlining
      }
      // Add self at the end, so the work loops pull it off again.
      add_work(old);
      return;
    }
    if( check_new(nnn) ) {      // If new, replace back in GVN
      nnn._live = old._live;    // Replacement has same liveness as original
      rereg(nnn, nnn.value(this));
    }
    if( !old.is_dead() ) { // if old is being replaced, it got removed from GVN table and types table.
      assert !check_opt(old);
      replace(old,nnn);
      nnn.keep();               // Keep-alive
      kill0(old);               // Delete the old n, and anything it uses
      add_work(nnn.unhook());   // Remove keep-alive and be sure to visit
    }
  }

  /** Look for a better version of 'n'.  Can change n's defs via the ideal()
   *  call, including making new nodes.  Can replace 'n' wholly, with n's uses
   *  now pointing at the replacement.
   *  @param n Node to be idealized; already in GVN
   *  @return null for no-change, or a better version of n, already in GVN */
  private Node xform_old0( Node n, int level ) {
    assert touched(n);          // Node is in type tables, but might be already out of GVN
    Type oldt = type(n);        // Get old type

    // Must exit either with {old node | null} and the old node in both types
    // and vals tables, OR exit with a new node and the old node in neither table.
    // [ts!] - Definitely in types table, [ts+] updated value in types
    // [vals?] - Maybe in vals table

    // [ts!,vals?] Check GVN tables first, because this is very fast and makes
    // good forward progress in computing value 'n'
    Node x = _vals.get(n);      // Check prior hit
    if( x != null && x != n ) return merge(n,x); // Keep merge

    // [ts!,vals?] Remove before ideal or value-wiring hacks edges & changes hash
    _vals.remove(n);

    assert n._uses._len>0 || n instanceof ScopeNode;

    // [ts!] Compute uses & live bits.  If progress, push the defs on the
    // worklist.  This is a reverse flow computation.
    TypeMem old = n._live;
    TypeMem nnn = n.live(this);
    if( old != nnn ) {          // Progress?
      assert nnn.isa(old);      // Monotonically improving
      n._live = nnn;            // Mark progress
      add_work_defs(n);         // Put defs on worklist... liveness flows uphill
    }

    // [ts!] If completely dead, exit now.
    if( !nnn.is_live() && !n.is_prim() && n.err(this)==null &&
        !(n instanceof CallNode) &&       // Keep for proper errors
        !(n instanceof UnresolvedNode) && // Keep for proper errors
        !(n instanceof RetNode) &&        // Keep for proper errors
        !(n instanceof ConNode) )         // Already a constant
      return untype(n, con(Type.ANY)); // Replace non-constants with high (dead) constants

    // [ts!] Compute best type, and type is IN ts
    Type t = n.value(this);     // Get best type

    // [ts!] Put updated types into table for use by ideal()
    if( t!=oldt ) {
      assert t.isa(oldt);       // Monotonically improving
      // [ts!] Replace with a constant, if possible.  This is also very cheap
      // (once we expensively computed best value) and makes the best forward
      // progress.
      if( replace_con(t,n) ) { unreg0(n); return con(t); }
      setype(n,t);
    }

    // [ts+] Try generic graph reshaping using updated types
    Node y = n.ideal(this,level);
    assert y==null || y==n || n._keep==0;// Ideal calls need to not replace 'keep'rs
    if( y != null && y != n      ) return untype(n, y  );  // Progress with some new node
    if( y != null && y.is_dead() ) return untype(n,null);

    // [ts+,vals?] Reinsert in GVN
    Node z = _vals.putIfAbsent(n,n);
    if( z != null && z != n ) return merge(n,z); // Keep merge

    // [ts+,vals!]
    assert check_opt(n);
    return oldt == t && y==null ? null : n; // Progress if types improved
  }

  // Utility: Merge old and new, returning node with the merged liveness.
  // Returns something monotonically 'more alive' than either.  Old is in the
  // type table and not in the vals table.  NNN is in both.
  private Node merge( Node old, Node nnn ) {
    nnn._live = (TypeMem)nnn._live.meet(old._live);
    Type told = type(old), tnnn = type(nnn);
    if( told!=tnnn ) { setype(nnn,told.join(tnnn)); add_work_uses(nnn); }
    return untype(old,nnn);      // Just toss old, keep nnn.
  }

  // Replace, but do not delete old.  Really used to insert a node in front of old.
  public void replace( Node old, Node nnn ) {
    while( old._uses._len > 0 ) {
      Node u = old._uses.del(0);  // Old use
      boolean was = touched(u);
      _vals.remove(u);  // Use is about to change edges; remove from type table
      u._chk();
      u._defs.replace(old,nnn); // was old now nnn
      nnn._uses.add(u);
      if( was ) {            // If was in GVN
        _vals.putIfAbsent(u,u);// Back in the table, since its still in the graph
        add_work(u);         // And put on worklist, to get re-visited
        if( u instanceof RetNode )
          add_work_uses(u); // really trying to get CallEpi to test trivial inline again
      }
    }
  }

  // Complete replacement; point uses to 'nnn'.  The goal is to completely replace 'old'.
  public Node subsume( Node old, Node nnn ) {
    replace(old,nnn);
    nnn.keep();                 // Keep-alive
    kill(old);                  // Delete the old n, and anything it uses
    return nnn.unhook();        // Remove keep-alive
  }

  // Once the program is complete, any time anything is on the worklist we can
  // always conservatively iterate on it.
  void iter(int opt_mode) {
    _opt_mode = opt_mode;
    assert Env.START.more_flow(this,new VBitSet(),true,0)==0; // Initial conditions are correct
    // As a debugging convenience, avoid inlining (which blows up the graph)
    // until other optimizations are done.  Gather the possible inline requests
    // and set them aside until the main list is empty, then work down the
    // inline list.
    //
    // As a coding/speed hack, do not try to find all nodes which respond to
    // control dominance changes during worklist iteration.  These can be very
    // far removed from the change point.  Collect and do them separately.
    NonBlockingHashMapLong<Node> can_doms = new NonBlockingHashMapLong<>();
    boolean did_doms=false;
    int cnt=0, wlen;
    while( (wlen=_work._len) > 0 || _work2._len > 0 ) {
      final boolean dom_small_work = wlen!=0;
      // Revisit all the possible control-dominance winners
      if( !dom_small_work ) {
        boolean old_doms=did_doms; did_doms=true;
        if( !old_doms ) { do_doms(can_doms); continue; }
      }
      // Turned on, fairly expensive assert
      assert dom_small_work || !Env.START.more_ideal(this,new VBitSet(),1); // No more small-work ideal calls to apply
      Node n = (dom_small_work ? _work : _work2).pop(); // Pull from main worklist before functions
      (dom_small_work ? _wrk_bits : _wrk2_bits).clear(n._uid);
      if( n.is_dead() ) continue;
      if( n._uses._len==0 && n._keep==0 ) { kill(n); continue; }
      if( can_dom(n) ) can_doms.put(n._uid,n);
      xform_old(n, dom_small_work ? 0 : 2);
      if( did_doms && _work._len != wlen-1 ) did_doms=false; // Did work, revisit doms
      // VERY EXPENSIVE ASSERT
      //assert Env.START.more_flow(this,new VBitSet(),true,0)==0; // Initial conditions are correct
      cnt++; assert cnt < 20000; // Catch infinite ideal-loops
    }
    // No more ideal calls, small or large, to apply
    assert !Env.START.more_ideal(this,new VBitSet(),3);
  }

  private boolean can_dom(Node n) {
    return n instanceof CastNode ||
      (n instanceof MProjNode && n.in(0) instanceof CallEpiNode);
  }
  private void do_doms(NonBlockingHashMapLong<Node> can_doms) {
    for( Node n : can_doms.values() )
      if( n.is_dead() ) can_doms.remove(n._uid);
      else add_work(n);
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
  public void gcp(ScopeNode rez ) {
    _opt_mode = 2;
    // Set all types to null (except primitives); null is the visit flag when
    // setting types to their highest value.
    _ts.fill(null);
    // Set all types to all_type().startype(), their most optimistic type.
    // This is mostly the dual(), except a the Start memory is always XOBJ.
    // Set all liveness to TypeMem.DEAD, their most optimistic type.
    walk_initype(Env.START);
    assert Env.START.more_flow(this,new VBitSet(),false,0)==0; // Initial conditions are correct
    // Prime the worklist
    rez.unhook(); // Must be unhooked to hit worklist
    add_work(rez);
    // Collect unresolved calls, and verify they get resolved.
    Ary<CallNode> ambi_calls = new Ary<>(new CallNode[1],0);

    // Repeat, if we remove some ambiguous choices, and keep falling until the
    // graph stabilizes without ambiguity.
    while( _work._len > 0 ) {
      // Analysis phase.
      // Work down list until all reachable nodes types quit falling
      while( _work._len > 0 ) {
        Node n = _work.pop();
        _wrk_bits.clear(n._uid);
        if( n.is_dead() ) continue; // Can be dead functions after removing ambiguous calls

        // Forwards flow
        Type ot = type(n);       // Old type
        Type nt = n.value(this); // New type
        if( ot != nt ) {         // Progress
          if( !check_monotonicity(n,ot,nt) ) continue; // Debugging hook
          _ts.setX(n._uid,nt);   // Record progress
          // Classic forwards flow on change:
          for( Node use : n._uses ) {
            assert use!=n; // Stop self-cycle (not legit, but happens during debugging)
            add_work(use); // Re-run users to check for progress
            // We may have a 'crossing optimization' point: changing the
            // pointer input to a Load or a Scope changes the memory demanded
            // by the Load or Scope.  This in turn changes the liveness fed
            // into the Load.  This might also be viewed as a "turn around"
            // point, where available value memory becomes demanded liveness.
            if( use.input_value_changes_live() )
              add_work_defs(use);

            // When new control paths appear on Regions, the Region stays the
            // same type (Ctrl) but the Phis must merge new values.
            if( use instanceof RegionNode )
              add_work_uses(use);
            // If a Parm:Mem input is updated, all Parm:ptrs may update.
            if( use instanceof ParmNode && ((ParmNode)use)._idx==-2 )
              add_work_uses(use.in(0));
          }
          if( n.value_changes_live() ) {
            add_work_defs(n);
            add_work_defs(n.in(2)); // Also Call.Unresolved: any resolved call makes that call alive
          }
          // Memory Parms enable sharpening all pointer-Parms.
          if( n instanceof ParmNode && ((ParmNode)n)._idx==-2 )
            add_work_uses(n.in(0));
          // Optimistic Call-Graph discovery.  If the funptr input lowers
          // to where a new FIDX might be possible, wire the CG edge.
          if( n instanceof CallEpiNode ) check_and_wire((CallEpiNode)n);
          for( Node use : n._uses )
            if( use instanceof CallEpiNode ) check_and_wire((CallEpiNode)use);
        }

        // Reverse flow
        TypeMem old = n._live;
        TypeMem nnn = n.live(this);
        if( old != nnn ) {      // Liveness progress
          assert old.isa(nnn);  // Monotonically improving
          n._live = nnn;
          add_work_defs(n);    // Put defs on worklist... liveness flows uphill
          if( n.live_changes_value() )
            add_work(n);
        }
        // See if we can resolve an unresolved
        if( n instanceof CallNode && n._live != TypeMem.DEAD ) {
          CallNode call = (CallNode)n;
          if( type(call.ctl()) == Type.CTRL && type(call) instanceof TypeTuple ) { // Wait until the Call is reachable
            BitsFun fidxs = CallNode.ttfp(type(call)).fidxs();
            if( fidxs.above_center() && fidxs.abit() == -1 && ambi_calls.find(call) == -1 )
              ambi_calls.add(call); // Track ambiguous calls
          }
        }
        // Very expensive assert
        //assert Env.START.more_flow(this,new VBitSet(),false,0)==0; // Initial conditions are correct
      }

      // Remove CallNode ambiguity after worklist runs dry
      while( !ambi_calls.isEmpty() ) {
        CallNode call = ambi_calls.pop();
        BitsFun fidxs = CallNode.ttfp(type(call)).fidxs();
        if( fidxs.abit() != -1    ) continue; // resolved to one
        if( !fidxs.above_center() ) continue; // resolved to many
        if( fidxs==BitsFun.ANY )    continue; // no choices, must be error
        FunPtrNode fptr = call.least_cost(this,fidxs);
        if( fptr==null ) continue;  // declared ambiguous, will be an error later
        call.set_fun_reg(fptr,this);// Set resolved edge
        add_work(call);
        add_work(fptr);             // Unresolved is now resolved and live
        // If this call is wired, a CallEpi will 'peek thru' an Unresolved to
        // pass liveness to a Ret.  Since 1-step removed from neighbor, have to
        // add_work 1-step further afield.
        add_work(fptr.in(0));
        assert Env.START.more_flow(this,new VBitSet(),false,0)==0; // Post conditions are correct
      }
    }

    // Revisit the entire reachable program, as ideal calls may do something
    // with the maximally lifted types.
    assert _wrk2_bits.isEmpty();
    walk_opt(rez);
    _wrk2_bits.clear();
    rez.keep();
    walk_dead(Env.START);
  }
  private void check_and_wire( CallEpiNode cepi ) {
    if( !cepi.check_and_wire(this) ) return;
    add_work(cepi.call());
    add_work(cepi);
    assert Env.START.more_flow(this,new VBitSet(),false,0)==0;
  }

  // Debugging hook
  private boolean check_monotonicity(Node n, Type ot, Type nt) {
    assert nt==nt.simple_ptr();   // Only simple pointers in node types
    if( ot.isa(nt) ) return true; // No bug
    add_work(n);                  // Setup for a re-run
    System.out.println("Not monotonic");
    return false;    // Just single-step forward in debugging to re-run n.value
  }

  // Forward reachable walk, setting types to all_type().dual() and making all dead.
  private void walk_initype( Node n ) {
    if( n==null || touched(n) ) return; // Been there, done that
    setype(n,Type.ANY);
    n._live = TypeMem.DEAD;     // Not alive
    // Walk reachable graph
    add_work(n);
    for( Node use : n._uses ) walk_initype(use);
    for( Node def : n._defs ) walk_initype(def);
  }

  // Node n is new during GCP
  public Node new_gcp( Node n ) {
    Node x = _vals.get(n);
    if( x!=null ) { kill0(n); return x; }
    _vals.put(n,n);
    n._live = TypeMem.DEAD;
    setype(n,n.value(this));
    add_work(n);
    return n;
  }


  // GCP optimizations on the live subgraph
  private void walk_opt( Node n ) {
    assert !n.is_dead();
    if( _wrk2_bits.tset(n._uid) ) return; // Been there, done that
    if( n==Env.START ) return;          // Top-level scope
    Type t = type(n);                   // Get optimistic computed type

    // Replace with a constant, if possible
    if( replace_con(t,n) )
      n=subsume(n,con(t));      // Constant replacement

    // Hit the fixed point, despite any immediate updates.  All prims are live,
    // even if unused so they might not have been computed
    assert n.value(this)==t;
    assert n.live(this)==n._live;

    // Walk reachable graph
    add_work(n);                        // Only walk once
    for( Node def : n._defs )
      if( def != null )
        walk_opt(def);
  }

  // Walk dead control and place on worklist
  private void walk_dead( Node n ) {
    assert !n.is_dead();
    if( _wrk_bits.get(n._uid) ) return; // Been there, done that
    add_work(n);                        // Only walk once
    for( Node use : n._uses ) walk_dead(use);
  }

  public Type sharptr( Node ptr, Node mem ) { return type(mem).sharptr(type(ptr)); }
}
