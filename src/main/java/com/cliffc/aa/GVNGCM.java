package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.BitSet;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import static com.cliffc.aa.AA.MEM_IDX;

// Global Value Numbering, Global Code Motion
public class GVNGCM {
  // Unique dense node-numbering
  private int CNT=1; // Do not hand out UID 0
  private final BitSet _live = new BitSet();  // Conservative approximation of live; due to loops some things may be marked live, but are dead

  public int uid() { assert CNT < 100000 : "infinite node create loop"; _live.set(CNT);  return CNT++; }

  public enum Mode {
    Parse   (false),          // Parsing
    PesiNoCG(false),          // Lifting, unknown Call Graph
    Opto    (true ),          // Falling, Call Graph discovery, no more code
    PesiCG  (true );          // Lifting,   known Call Graph
    public final boolean _CG; // True if full CG is known or being discovered.  Only for whole programs during or after Opto.
    Mode(boolean CG) { _CG=CG; }
  }
  public Mode _opt_mode=Mode.Parse;

  // Iterative worklist
  private final Ary<Node> _work = new Ary<>(new Node[1], 0);
  private final BitSet _wrk_bits = new BitSet();

  public Node add_work( Node n ) { if( n != null && !_wrk_bits.get(n._uid) ) add_work0(n); return n;}
  private <N extends Node> N add_work0( N n ) {
    _work.add(n);               // These need to be visited later
    _wrk_bits.set(n._uid);
    return n;
  }

  public boolean on_work( Node n ) { return _wrk_bits.get(n._uid) || _wrk3_bits.get(n._uid); }
  // Add all uses as well
  public void add_work_uses( Node n ) {
    for( Node use : n._uses )  add_work(use);
    // Add self at the end, so the work loops pull it off again.
    if( n._in ) add_work(n); // Do not re-add if mid-ideal-call.
  }
  // All defs on worklist - liveness flows uphill
  public void add_work_defs( Node n ) {
    for( Node def : n._defs ) // Put defs on worklist... liveness flows uphill
      if( def != null && def != n )
        add_work(def);
  }
  void add_work    (    TNode  dep ) {                                         add_work((Node)dep); }
  void add_work_all(Ary<TNode> deps) { if( deps!=null ) for( TNode tn : deps ) add_work((Node)tn); }

  // A second worklist, for code-expanding and thus lower priority work.
  // Inlining happens off this worklist, once the main worklist runs dry.
  private final Ary<Node> _work2 = new Ary<>(new Node[1], 0);
  private final VBitSet _wrk2_bits = new VBitSet();
  public void add_work2( Node n ) {
    if( !_wrk2_bits.tset(n._uid) )
      _work2.add(n);
  }
  // A third worklist.
  // As a coding/speed hack, do not try to find all nodes which respond to
  // control dominance changes during worklist iteration.  These can be very
  // far removed from the change point.  Collect and do them separately.
  private final Ary<Node> _work3 = new Ary<>(new Node[1], 0);
  private final VBitSet _wrk3_bits = new VBitSet();
  public void add_work3( Node n ) {
    if( !_wrk3_bits.tset(n._uid) )
      _work3.add(n);
  }

  // Global expressions, to remove redundant Nodes
  private final ConcurrentHashMap<Node,Node> _vals = new ConcurrentHashMap<>();
  Set<Node> valsKeySet() { return _vals.keySet(); }

  // Initial state after loading e.g. primitives.
  public static int _INIT0_CNT;
  void init0() {
    assert _live.get(CNT-1) && !_live.get(CNT) && _work._len==0 && _wrk_bits.isEmpty();
    _INIT0_CNT=CNT;
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  void reset_to_init0() {
    _work .clear(); _wrk_bits .clear();
    _work2.clear(); _wrk2_bits.clear();
    _opt_mode = Mode.Parse;
    CNT = 0;
    _live.clear();
    _vals.clear();
  }

  // Make globally shared common ConNode for this type.
  public @NotNull ConNode con( Type t ) {
    // Check for a function constant, and return the globally shared common
    // FunPtrNode instead.  This only works for FunPtrs with no closures.
    assert !(t instanceof TypeFunPtr && t.is_con()); // Does not work for function constants
    assert t==t.simple_ptr();
    ConNode con = new ConNode<>(t);
    Node con2 = _vals.get(con);
    if( con2 != null ) {        // Found a prior constant
      kill0(con);               // Kill the just-made one
      con = (ConNode)con2;
    } else {
      con.set_val(t);           // In the GVN system
      _vals.put(con,con);
    }
    con._live = TypeMem.LIVE_BOT; // Alive, but demands no memory
    add_work(con);
    return con;
  }

  // Record a Node, but do not optimize it for value and ideal calls, as it is
  // mid-construction from the parser.  Any function call with yet-to-be-parsed
  // call sites, and any loop top with an unparsed backedge needs to use this.
  public <N extends Node> N init( N n ) {
    n.set_val(Type.ALL);
    assert n._uses._len==0;
    return init0(n);
  }
  <N extends Node> N init0( N n ) {
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

  // Remove from GVN structures.  Used rarely for whole-merge changes
  public Type unreg( Node n ) { assert check_opt(n); return unreg0(n); }
  private Type unreg0( Node n ) {
    Type t = n.val();           // Get old type
    n._in = false;              // Remove from type system
    _vals.remove(n);            // Remove from GVN
    return t;
  }

  // Used rarely for whole-merge changes
  public void rereg( Node n, Type oldt ) {
    assert !check_opt(n);
    n.set_val(oldt);
    _vals.putIfAbsent(n,n);     // 'n' will not go back if it hits a prior
    add_work_uses(n);
  }

  // Did a bulk not-monotonic update.  Forcibly update the entire region at
  // once; restores monotonicity over the whole region when done.
  public void revalive(Node... ns) {
    for( Node n : ns ) {
      if( n == null ) continue;
      Type t = n.value(_opt_mode);
      if( t != n.val() ) {
        n.set_val(t);
        add_work_uses(n);
      }
    }
    for( int i=ns.length-1; i>=0; i-- ) {
      Node n = ns[i];
      if( n==null ) continue;
      TypeMem t = n.live(_opt_mode);
      if( t != n._live ) { n._live=t; add_work_defs(n); }
    }
  }

  // Hack an edge, updating GVN as needed
  public Node set_def_reg(Node n, int idx, Node def) {
    _vals.remove(n);            // Remove from GVN
    n.set_def(idx,def,this);    // Hack edge
    if( n.is_dead() ) return null;
    assert !check_gvn(n,false); // Check not in GVN table after hack
    _vals.put(n,n);             // Back in GVN table
    return add_work(n);
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
    if( n._in ) {               // First & only test: in type table or not
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
      Type t = n.value(_opt_mode); // Get best type
      // Replace with a constant, if possible
      if( replace_con(t,n) )
        { kill_new(n); return con(t); }
      n.set_val(t);               // Set it in for ideal
      Node x = n.ideal(this,0);
      if( x == null ) break;
      if( x != n ) {          // Different return, so delete original dead node
        if( n._uses._len==0 ) {
          x.keep();           // Keep alive during deletion of n
          kill(n);            // replace so immediately recycle n and dead subgraph
          x.unhook();         // Remove keep-alive
        }
        n=x;
        if( !check_new(x) ) return x; // If the replacement is old, no need to re-ideal
        add_work_defs(n);       // Force live-ness rechecking
      }
      n._in=false;              // Pull out for invariants on next iteration
      cnt++; assert cnt < 100;  // Catch infinite ideal-loops
    }
    // Global Value Numbering; n is "in the system" now
    Node x = _vals.putIfAbsent(n,n);
    if( x != null ) { n._in=false; x._live=(TypeMem)n._live.meet(x._live); kill_new(n); return x; }
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
    if( n._keep >0 || n instanceof ConNode || n instanceof ErrNode || n.is_prim() )
      return false; // Already a constant, or never touch an ErrNode
    // Constant argument to call: keep for call resolution.
    // Call can always inline to fold constant.
    if( n instanceof ProjNode && n.in(0) instanceof CallNode )
      return false;
    // Is in-error; do not remove the error.
    if( n.err(true) != null )
      return false;
    // Is a constant (or could be)
    if( !t.is_con() ) {
      if( t instanceof TypeFunPtr && !(n instanceof FunPtrNode) )
        return ((TypeFunPtr)t).can_be_fpnode();
      return false;
    }
    return true; // Replace with a ConNode
  }

  public void xform_old( Node old, int level ) {
    Node nnn = xform_old0(old,level);
    if( nnn==null ) return;     // No progress
    assert (level&1)==0;        // No changes during asserts
    // Progress, so changes to the users which might change live-use-ness.
    if( !old.is_dead() )
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
        if( use instanceof DefMemNode )
          add_work_uses(use); // Changing input to DefMem impacts all CallEpi
        if( use instanceof ParmNode && ((ParmNode)use)._idx==MEM_IDX )
          add_work_uses(use.in(0));  // Recheck memory sharpening of adjacent Parms
        if( use instanceof MProjNode && ((MProjNode)use)._idx==0 && use._uses.at(0) instanceof MemJoinNode )
          add_work(use._uses.at(0));
        if( old instanceof CallNode && use instanceof CallEpiNode )
          for( Node useuse : use._uses )
            if( useuse instanceof MProjNode )
              for( Node useuseuse : useuse._uses )
                if( useuseuse instanceof LoadNode )
                  add_work(useuseuse); // Final load bypassing a Call
        if( old instanceof CallNode && use instanceof CProjNode )
          for( Node useuse : use._uses )
            if( useuse instanceof FunNode )
              add_work(useuse); // Call lifts TFP, some FunNodes no longer called, go dead
        if( use.is_multi_head() )
          for( Node useuse : use._uses ) {
            if( useuse instanceof ProjNode && use.is_copy(((ProjNode) useuse)._idx) != null )
              add_work(useuse);
            if( useuse instanceof CallEpiNode )
              add_work(useuse);
          }
        if( use instanceof NewStrNode.AddStrStr )
          for( Node defuse : use._defs )
            if( defuse != old )
              add_work(defuse);
      }
      if( old instanceof ProjNode && old.in(0) instanceof NewNode )
        add_work(Env.DEFMEM);
      if( old.value_changes_live() )
        add_work_defs(old);
      // Add self at the end, so the work loops pull it off again.
      add_work(old);
      return;
    }
    if( !nnn.is_dead() && check_new(nnn) ) { // If new, replace back in GVN
      nnn._live = old._live;    // Replacement has same liveness as original
      rereg(nnn, nnn.value(_opt_mode));
    }
    if( !old.is_dead() ) { // if old is being replaced, it got removed from GVN table and types table.
      assert !check_opt(old);
      if( nnn._live != old._live ) {                    // New is as alive as the old
        nnn._live = (TypeMem)nnn._live.meet(old._live); // Union of liveness
        add_work_defs(nnn);                             // Push liveness uphill
      }
      add_work(subsume0(old,nnn)); // Subsume 'old' with 'nnn' and nuke 'old'.
    }
  }

  /** Look for a better version of 'n'.  Can change n's defs via the ideal()
   *  call, including making new nodes.  Can replace 'n' wholly, with n's uses
   *  now pointing at the replacement.
   *  @param n Node to be idealized; already in GVN
   *  @return null for no-change, or a better version of n, already in GVN */
  private Node xform_old0( Node n, int level ) {
    assert n._in;    // Node is in type tables, but might be already out of GVN
    Type oval = n._val; // Get old type

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

    // Perform unification
    boolean hm_progress = n.unify(false);

    // [ts!] Compute uses & live bits.  If progress, push the defs on the
    // worklist.  This is a reverse flow computation.
    TypeMem oliv = n._live;
    TypeMem nliv = n.live(_opt_mode);
    if( oliv != nliv ) {        // Progress?
      assert nliv.isa(oliv);    // Monotonically improving
      n._live = nliv;           // Mark progress
      add_work_defs(n);         // Put defs on worklist... liveness flows uphill
    }

    // [ts!] If completely dead, exit now.
    if( !nliv.is_live() && !n.is_prim() && n.err(true)==null && n._keep==0 &&
        !(n instanceof CallNode) &&       // Keep for proper errors
        !(n instanceof UnresolvedNode) && // Keep for proper errors
        !(n instanceof RetNode) &&        // Keep for proper errors
        !(n instanceof ConNode) ) {       // Already a constant
      n._in=false;          // Replace non-constants with high (dead) constants
      return con(Type.ANY);
    }

    // [ts!] Compute best type, and type is IN ts
    Type nval = n.value(_opt_mode); // Get best type

    // [ts!] Put updated types into table for use by ideal()
    if( nval!=oval ) {
      assert nval.isa(oval);    // Monotonically improving
      n.set_val(nval);
    }
    // [ts!] Replace with a constant, if possible.  This is also very cheap
    // (once we expensively computed best value) and makes the best forward
    // progress.
    if( replace_con(nval,n) ) { unreg0(n); return con(nval); }

    // [ts+] Try generic graph reshaping using updated types
    Node y = n.ideal(this,level);
    assert y==null || y==n || n._keep==0;// Ideal calls need to not replace 'keep'rs
    if( y != null && y != n      ) { n._in=false; return  y  ; } // Progress with some new node
    if( y != null && y.is_dead() ) { n._in=false; return null; }

    // [ts+,vals?] Reinsert in GVN
    Node z = _vals.putIfAbsent(n,n);
    if( z != null && z != n ) return merge(n,z); // Keep merge

    // [ts+,vals!]
    assert check_opt(n);
    return oval == nval && oliv == nliv && y==null && !hm_progress ? null : n; // Progress if types improved
  }

  // Utility: Merge old and new, returning node with the merged liveness.
  // Returns something monotonically 'more alive' than either.  Old is in the
  // type table and not in the vals table.  NNN is in both.
  private Node merge( Node old, Node nnn ) {
    nnn._live = (TypeMem)nnn._live.meet(old._live);
    Type told = old.val(), tnnn = nnn.val();
    if( told!=tnnn ) { nnn.set_val(told.join(tnnn)); add_work_uses(nnn); }
    old._in=false;              // Just toss old
    return nnn;                 // Keep nnn.
  }

  // Complete replacement; point uses to 'nnn' and removes 'old'.
  public Node subsume( Node old, Node nnn ) { unreg0(old); return subsume0(old,nnn); }
  public Node subsume0( Node old, Node nnn ) {
    assert !nnn.is_dead();
    // When replacing one node with another, unify their type vars
    if( !old.is_dead() ) old.tvar().unify(nnn.tvar(), false);
    insert(old,nnn);            // Change graph shape
    nnn.keep();                 // Keep-alive
    kill0(old);                 // Delete the old n, and anything it uses
    return nnn.unhook();        // Remove keep-alive
  }

  // Replace, but do not delete old.  Really used to insert a node in front of
  // old.  Does graph-structure changes, making pointers-to-old point to nnn.
  // Changes neither 'old' nor 'nnn'.  Does not enforce any monotonicity nor
  // unification.
  public void insert( Node old, Node nnn ) {
    while( old._uses._len > 0 ) {
      Node u = old._uses.del(0);  // Old use
      boolean was = u._in;
      _vals.remove(u);  // Use is about to change edges; remove from type table
      u._chk();
      u._defs.replace(old,nnn); // was old now nnn
      nnn._uses.add(u);
      if( was ) {            // If was in GVN
        _vals.putIfAbsent(u,u);// Back in the table, since its still in the graph
        add_work(u);         // And put on worklist, to get re-visited
        add_work_insert_use(nnn,u);
      }
    }
  }

  // Add selected users of 'old' when replaced by 'nnn' to trigger more ideal() calls.
  private void add_work_insert_use(Node nnn, Node u) {
    if( u instanceof RetNode )
      add_work_uses(u); // really trying to get CallEpi to test trivial inline again
    if( u instanceof MemSplitNode ) {
      Node puse = ProjNode.proj(u, 0);
      if( puse != null ) add_work_uses(puse);
    }
    if( u instanceof RegionNode )
      for( Node useuse : u._uses )
        if( useuse instanceof PhiNode )
          add_work(useuse);
    if( nnn instanceof MProjNode && nnn.in(0) instanceof MemSplitNode )
      add_work_uses(u); // Trying to get Join/Merge/Split to fold up
    if( u instanceof StoreNode ) // Load/Store fold up
      for( Node n : u._uses ) if( n instanceof LoadNode ) add_work(n);
    if( u instanceof CallNode )
      for( Node n : u._uses ) if( n instanceof CallEpiNode ) add_work(n);
    if( u instanceof DefMemNode )
      add_work_uses(u); // Killing a New triggers value rollups on most CallEpis
    if( nnn.in(0) != null ) add_work(nnn.in(0));
  }

  // Once the program is complete, any time anything is on the worklist we can
  // always conservatively iterate on it.
  void iter(Mode opt_mode) {
    _opt_mode = opt_mode;
    assert Env.START.more_flow(this,new VBitSet(),true,0)==0; // Initial conditions are correct
    // As a debugging convenience, avoid inlining (which blows up the graph)
    // until other optimizations are done.  Gather the possible inline requests
    // and set them aside until the main list is empty, then work down the
    // inline list.
    boolean did_doms=true;
    int cnt=0, wlen;
    while( (wlen=_work._len) > 0 || _work2._len > 0 || _work3._len > 0 ) {
      boolean dom_small_work = wlen!=0;
      // As a coding/speed hack, do not try to find all nodes which respond to
      // control dominance changes during worklist iteration.  These can be
      // very far removed from the change point.  Collect and do them
      // separately.  Revisit all the possible control-dominance winners.
      if( !dom_small_work ) { // No work
        if( !did_doms ) { _work.addAll(_work3); _wrk_bits.or(_wrk3_bits); did_doms=true; dom_small_work=(wlen=_work._len)!=0; }
        _work3.clear(); _wrk3_bits.clear();
        if( _work._len == 0 && _work2._len == 0 ) break;
      }
      // Turned on, fairly expensive assert
      assert dom_small_work || !Env.START.more_ideal(this,new VBitSet(),1); // No more small-work ideal calls to apply
      Node n = (dom_small_work ? _work : _work2).pop(); // Pull from main worklist before functions
      (dom_small_work ? _wrk_bits : _wrk2_bits).clear(n._uid);
      if( n.is_dead() ) continue;
      if( n._uses._len==0 && n._keep==0 ) { kill(n); continue; }
      if( can_dom(n) ) add_work3(n);
      xform_old(n, dom_small_work ? 0 : 2);
      if( did_doms && _work._len != wlen-1 ) did_doms=false; // Did work, revisit doms
      // VERY EXPENSIVE ASSERT
      //assert Env.START.more_flow(this,new VBitSet(),true,0)==0; // Initial conditions are correct
      cnt++; assert cnt < 35000; // Catch infinite ideal-loops
    }
    // No more ideal calls, small or large, to apply
    assert !Env.START.more_ideal(this,new VBitSet(),3);
    assert _work3.isEmpty();
    assert FunNode._must_inline==0;
  }

  private boolean can_dom(Node n) {
    return n instanceof LoadNode || n instanceof StoreNode ||
      n instanceof CastNode ||
      (n instanceof MProjNode && n.in(0) instanceof CallEpiNode);
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
    Env.START.walk_initype(this,new VBitSet());
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
        Type oval = n._val;                                // Old local type
        Type nval = n.value(_opt_mode);                    // New type
        if( oval != nval ) {                               // Progress
          if( !check_monotonicity(n,oval,nval) ) continue; // Debugging hook
          n.set_val(nval);           // Record progress
          // Classic forwards flow on change:
          for( Node use : n._uses ) {
            if( use==n ) continue; // Stop self-cycle (not legit, but happens during debugging)
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
            if( use instanceof RegionNode || use instanceof CallNode )
              add_work_uses(use);
            // If a Parm:Mem input is updated, all Parm:ptrs may update.
            if( use instanceof ParmNode && ((ParmNode)use)._idx==MEM_IDX )
              add_work_uses(use.in(0));
            if( n instanceof CallNode && use instanceof CProjNode )
              add_work_uses(use); // Call lowers fidxs, Funs might get turned on
            if( use instanceof DefMemNode ) add_work_uses(use);
          }
          if( n.value_changes_live() ) {
            add_work_defs(n);
            add_work_defs(n.in(2)); // Also Call.Unresolved: any resolved call makes that call alive
          }
          // Memory Parms enable sharpening all pointer-Parms.
          if( n instanceof ParmNode && ((ParmNode)n)._idx==MEM_IDX )
            add_work_uses(n.in(0));
          // Optimistic Call-Graph discovery.  If the funptr input lowers
          // to where a new FIDX might be possible, wire the CG edge.
          if( n instanceof CallEpiNode ) check_and_wire((CallEpiNode)n);
          for( Node use : n._uses )
            if( use instanceof CallEpiNode ) check_and_wire((CallEpiNode)use);
        }

        // Reverse flow
        TypeMem oliv = n._live;
        TypeMem nliv = n.live(_opt_mode);
        if( oliv != nliv ) {      // Liveness progress
          if( !check_monotonicity(n,oliv,nliv) ) continue; // Debugging hook
          n._live = nliv;
          add_work_defs(n);    // Put defs on worklist... liveness flows uphill
          if( n.live_changes_value() )
            add_work(n);
          if( n instanceof  ProjNode && n.in(0) instanceof CallNode )
            add_work_defs(n.in(0)); // Args are alive, if Call Projs are alive
          if( n instanceof CProjNode && n.in(0) instanceof CallEpiNode )
            add_work(((CallEpiNode)n.in(0)).call());
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
              add_work(call);
            }
          }
        }
        // Very expensive assert
        //assert Env.START.more_flow(this,new VBitSet(),false,0)==0; // Initial conditions are correct
      }

      // Remove CallNode ambiguity after worklist runs dry.  This makes a
      // 'least_cost' choice on unresolved Calls, and lowers them in the
      // lattice... allowing more GCP progress.
      while( !ambi_calls.isEmpty() )
        remove_ambi(ambi_calls.pop());
    }

    // Revisit the entire reachable program, as ideal calls may do something
    // with the maximally lifted types.
    assert _wrk2_bits.isEmpty();
    walk_opt(rez);
    _wrk2_bits.clear();
    rez.keep();
    walk_dead(Env.START);
  }

  private void remove_ambi( CallNode call ) {
    TypeFunPtr tfp = CallNode.ttfpx(call.val());
    FunPtrNode fptr = null;
    if( tfp != null ) {     // Have a sane function ptr?
      BitsFun fidxs = tfp.fidxs();
      if( !fidxs.above_center() ) return; // Resolved after all
      if( fidxs!=BitsFun.ANY )            // And have choices
        // Pick least-cost among choices
        fptr = call.least_cost(this,fidxs,call.fdx());
    }
    if( fptr==null ) {          // Not resolving, program is in-error
      call._not_resolved_by_gcp = true;
      add_work(call);
      add_work(call.fdx());
      return;                   // Not resolving, but Call flagged as in-error
    }
    set_def_reg(call,AA.FUN_IDX,fptr.display());
    call.set_fdx_reg(fptr,this);// Set resolved edge
    add_work(call);
    add_work(call.cepi());
    revalive(add_work(fptr)); // Unresolved is now resolved and live, and might lift from ESCAPE to LIVE
    add_work(fptr.fun());
    // If this call is wired, a CallEpi will 'peek thru' an Unresolved to
    // pass liveness to a Ret.  Since 1-step removed from neighbor, have to
    // add_work 1-step further afield.
    add_work(fptr.in(0));
    assert Env.START.more_flow(this,new VBitSet(),false,0)==0; // Post conditions are correct
  }

  private void check_and_wire( CallEpiNode cepi ) {
    if( !cepi.check_and_wire(this) ) return;
    add_work(cepi.call().fdx());
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

  // Node n is new during GCP
  public Node new_gcp( Node n ) {
    Node x = _vals.get(n);
    if( x!=null ) { kill0(n); return x; }
    _vals.put(n,n);
    n.set_val(n.value(_opt_mode));
    n._live = TypeMem.DEAD;
    add_work(n);
    return n;
  }


  // GCP optimizations on the live subgraph
  private void walk_opt( Node n ) {
    assert !n.is_dead();
    if( _wrk2_bits.tset(n._uid) ) return; // Been there, done that
    if( n==Env.START ) return;          // Top-level scope

    // Hit the fixed point, despite any immediate updates.
    assert n.value(_opt_mode)== n._val;
    assert n.live (_opt_mode)==n._live;

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
}
