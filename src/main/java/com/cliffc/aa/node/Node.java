package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.HashSet;
import java.util.Arrays;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntSupplier;
import java.util.function.Predicate;

import static com.cliffc.aa.Env.GVN;
import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.node.FunNode._must_inline;

// Sea-of-Nodes
public abstract class Node implements Cloneable, IntSupplier {

  // --------------------------------------------------------------------------
  // Unique dense node-numbering
  public int _uid;      // Unique ID, will have gaps, used to give a dense numbering to nodes

  // Source of unique ids
  private static int CNT=1; // Do not hand out UID 0
  int newuid() {
    assert CNT < 100000 : "infinite node create loop";
    if( CNT==AA.UID )
      System.out.print("");     // Handy break-at-UID
    return CNT++;
  }
  @Override public int getAsInt() { return _uid; }
  
  // Utility during debugging to find a reachable Node by _uid
  public  Node find( int uid ) { return find(uid,new VBitSet()); }
  private Node find( int uid, VBitSet bs ) {
    if( _uid==uid ) return this;
    if( bs.tset(_uid) || isDead() ) return null;
    Node m;
    for( Node n : _defs ) if( n!=null && (m=n.find(uid,bs)) !=null ) return m;
    for( Node n : _uses ) if(            (m=n.find(uid,bs)) !=null ) return m;
    return null;
  }

  
  public static int _PRIM_CNT = 99999;
  // Initial state after loading e.g. primitives.
  public static void init0() { _PRIM_CNT=CNT; }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  public static void reset_to_init0() { CNT = _PRIM_CNT; }

  // Is a primitive
  public boolean always_prim() { return _uid<_PRIM_CNT; }
  public boolean isPrim() { return always_prim() && PrimNode.post_init(); }

  // Overridden in subclasses that return TypeTuple value types.  Such nodes
  // are always followed by ProjNodes to break out the tuple slices.  If the
  // node optimizes, each ProjNode becomes a copy of some other value... based
  // on the ProjNode index
  public Node isCopy(int idx) { return null; }

  // Only true for Unresolved
  public boolean is_forward_ref() { return false; }
  // Only true for a bare StructNode
  public boolean is_forward_type() { return false; }

  // True if normally (not in-error) produces a TypeMem value or a TypeTuple
  // with a TypeMem at(MEM_IDX).
  public boolean isMem() { return false; }

  // Region has Phis, Fun has Parms, If as 2 Controls, Call & CallEpi have many Projs
  public boolean isMultiHead() { return false; }
  
  // Region, Fun, If, Return, Call, CallEpi
  public boolean isCFG() { return false; }

  // --------------------------------------------------------------------------
  // Node pretty-print info

  // String label; interned; unique per node class, but might be more refined
  // than just class name.  E.g. "Add" or "Phi_Mem" or "Call_foo"
  abstract String label();

  // TODO: Graphic print e.g. greek letter Phi for PhiNodes
  
  // --------------------------------------------------------------------------
  // Primitive edge management.  Add and remove edges in a single direction.
  
  // Defs.  Generally fixed length, ordered, nulls allowed, no unused trailing
  // space.  Zero is Control.
  private Node[] _defs;         // Array of defs
  private int _len;             // The in-use part of defs
  public int len() { return _len; }
  public Node in( int i) { assert i<_len; return _defs[i]; }
  public Node last() { return _defs[_len-1]; }

  // Add a def, making more space as needed.
  private void _addDef( Node n ) {
    // A NPE here means the _defs are null, which means the Node was killed
    if( _len == _defs.length ) {
      int len = Integer.numberOfLeadingZeros(_len);
      while( len < _len ) len<<=1;
      _defs = Arrays.copyOf(_defs,len);
    }
    _defs[_len++] = n;
  }

  // Return the def index or -1
  public int findDef( Node def ) {
    for( int i=0; i<_len; i++ )  if( _defs[i]==def )  return i;
    return -1;
  }

  public NodeUtil.Iter defs() { return NodeUtil.Iter.get(_defs,_len); }

  void swap_last() {
    Node tmp = _defs[_len-2];
    _defs[_len-2] = _defs[_len-1];
    _defs[_len-1] = tmp;
  }
  
  // Uses.  Generally variable length, unordered, nulls allowed as a "keep
  // alive" flag.
  private Node[] _uses;         // Array of uses
  private int _ulen;            // The in-use part of uses

  public int nUses() { return _ulen; }
  public Node use0() { return _uses[0]; }
  // Add a use, making more space as needed.
  private void _addUse( Node n ) {
    // A NPE here means the _uses are null, which means the Node was killed
    if( _ulen == _uses.length ) {
      int len = Integer.numberOfLeadingZeros(_ulen);
      while( len < _ulen ) len<<=1;
      _uses = Arrays.copyOf(_uses,len);
    }
    _uses[_ulen++] = n;
  }

  // Delete a use, which must exist.
  private void _delUse( Node n ) {
    // NPE here if 'this' is dead
    int idx = findUse(n);
    // AIOOBE here if 'n' was not found
    _uses[idx] = _uses[--_ulen];
  }

  // Find use.  Backwards scan, because most recent found was probably also
  // most recently added.
  public int findUse( Node use ) {
    for( int i=_ulen-1; i<=0; i-- )  if( _uses[i]==use )  return i;
    return -1;
  }

  public NodeUtil.Iter uses() { return NodeUtil.Iter.get(_uses,_ulen); }

  public boolean isDead() { return _uses == null; }

  // Keep track of "keep" Nodes during parsing, and assert that the keep/unkeep
  // happens in balanced pairs is in the Parser
  public <N extends Node> N   keep() { _addUse(null); return (N)this;  }
  public <N extends Node> N unkeep() { _delUse(null); return (N)this;  }
  boolean isKeep() { return findUse(null) != -1; }

  
  // --------------------------------------------------------------------------
  // Bi-directional edge management, including hash changes forcing GVN
  
  // Edge-lock: cannot modify edges because messes up hashCode & GVN
  private boolean _elock; 

  // Global expressions, to remove redundant Nodes
  public static final ConcurrentHashMap<Node,Node> VALS = new ConcurrentHashMap<>();

  // Edge lock check, or anything else that changes the hash.
  // Clear the lock and remove from VALS
  public void unelock() {
    if( _elock ) {              // Edge-locked
      _elock=false;             // Unlock
      Node x = VALS.remove(this);
      assert x==this;           // Got the right node out
    }
  }

  // Check the elock is consistent, lock and insert into VALS
  public Node _elock() {        // No assert version, used for new nodes
    if( _elock ) { assert VALS.get(this)==this; return this; }
    assert VALS.get(this)==null;
    _elock = true;
    VALS.put(this,this);
    return this;
  }
  
  // Add def/use edge.  Updates both sides of the graph, and since the hash
  // changes removes 'this' from the GVN VALS table.
  public Node addDef(Node n) {
    unelock();
    _addDef(n);
    if( n!=null ) n._addUse(this);
    return this;
  }
  
  // Replace def/use edge.  Updates both sides of the graph, and since the hash
  // changes removes 'this' from the GVN VALS table.  The old def loses a use
  // and may be recursively deleted.  Returns 'this'.
  public Node setDef( int idx, Node n ) {
    unelock();
    Node old = in(idx);  // Get old value
    // Add edge to new guy before deleting old, in case old goes dead and
    // recursively makes new guy go dead also
    if( (_defs[idx] = n) != null ) n._addUse(this);
    return _unuse(old);
  }

  // Delete def by index, preserving edges but not order
  Node del( int idx ) {
    unelock();
    Node n = _defs[idx];
    _defs[idx] = _defs[--_len];
    _unuse(n);
    return n;
  }

  // Remove last def and return it.
  public Node pop( ) { return del(_len-1); }

  // Delete 1st instanceof named def; error if not found.
  // Does not preserve order.
  public Node del( Node def ) { return del(findDef(def)); }

  
  // Replace, but do not delete this.  Really used to insert a node in front of
  // this.   Does graph-structure changes, making pointers-to-this point to nnn.
  // Changes neither 'this' nor 'nnn'.  Does not enforce any monotonicity nor
  // unification.
  public void insert( Node nnn ) {
    assert !nnn.isDead();
    if( _ulen>0 ) unelock(); // Hacking edges
    while( _ulen > 0 ) {
      Node u = _uses[--_ulen];  // Old use
      u._defs[u.findDef(this)] = nnn;// was this now nnn
      nnn._addUse(u);
    }
  }

  // Complete replacement; point uses to 'nnn' and removes 'this'.
  public void subsume( Node nnn ) {
    insert(nnn);
    kill();                     // Delete the old, and anything it uses
  }

  // Kill a node; all inputs are null'd out; this may put more dead Nodes on
  // the dead worklist.  Return this for progress, null for no-progress.
  // Co-recursive with _unuse.
  public Node kill( ) {
    assert !isPrim();
    if( isDead() ) return this;
    assert _ulen==0;
    deps_work_clear();          // Put dependents on worklist
    unelock();
    Node[] defs = _defs;
    while( _len > 0 ) _unuse(defs[--_len]);
    _defs = _uses = null;       // Poor-man's indication of a dead node, before killing recursively
    return this;
  }

  // Already nuked the this->old edge, now nuke the old->this edge and
  // recursively kill if unused.  Returns this.  Co-recursive with kill.
  private Node _unuse( Node old ) {
    if( old == null ) return this;
    old._delUse(this);
    // Either last use of old & goes dead, or at least 1 fewer uses & changes liveness
    if( old._ulen==0 ) old.kill();
    //else GVN.add_flow_reduce(old);
    return this;
  }

  // Check before killing 'this' and return 'n'.
  public Node kill( Node n ) {
    if( n == this || _ulen>0 ) return n;
    n.keep();
    kill();
    return n.unkeep();
  }


  //public Node insert (int idx, Node n) { unelock(); _defs.insert(idx,n); if( n!=null ) n._uses.add(this); return this; }
  //// Return Node at idx, withOUT auto-deleting it, even if this is the last
  //// use.  Used by the parser to retrieve final Nodes from tmp holders.  Does
  //// NOT preserve order.
  
  //// Remove Node at idx, auto-delete and preserve order.
  //public Node remove(int idx) { unelock(); return unuse(_defs.remove(idx)); }
  //// Remove Node, auto-delete and preserve order.  Error if not found
  //public Node remove(Node x) { return remove(_defs.find(x)); }

  //public void replace(Node old, Node nnn) { unelock(); _defs.replace(old,nnn); }


  
  // TODO: Yanked as too fancy during parsing
  //// Keep a Node alive during all optimizations, because future direct uses
  //// will yet appear.  The Node can otherwise be fully optimized and replaced
  //// with equivalents.  The push/pop sequences are strongly asserted for stack
  //// order.
  //
  //public int push() { return GVNGCM.push(this); }
  //public static Node pop (int idx) { assert idx==GVNGCM.KEEP_ALIVE._defs._len;  return GVNGCM.pop(idx); }
  //public static Node peek(int idx) { assert idx<=GVNGCM.KEEP_ALIVE._defs._len;  return GVNGCM.KEEP_ALIVE.in(idx-1); }
  //public static void pops(int nargs) { for( int i=0; i<nargs; i++ ) GVNGCM.KEEP_ALIVE.pop(); }
  //public boolean isKeep() {
  //  for( Node use : _uses ) if( use instanceof KeepNode )  return true;
  //  return false;
  //}
  
  // Hash is function+inputs, or opcode+input_uids, and is invariant over edge
  // order (so we can swap edges without rehashing)
  @Override public int hashCode() {
    int sum = label().hashCode();
    for( Node def : defs() ) if( def != null ) sum ^= def._uid;
    return sum;
  }
  // Equals is function+inputs, or opcode+input_uids.  Uses pointer-equality
  // checks for input equality checks.
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof Node n) ) return false;
    if( !Util.eq(label(), n.label()) ) return false;
    if( _len != n._len ) return false;
    // Note pointer-equality
    for( int i=0; i<_len; i++ ) if( _defs[i] != n._defs[i] ) return false;
    return true;
  }
 
  // --------------------------------------------------------------------------
  // Forward flow type tracking
  
  public Type _val;     // Value; starts at ALL and lifts towards ANY.

  // Compute the current best Type for this Node, based on the types of its
  // inputs.  May return Type.ALL, especially if its inputs are in error.  It
  // must be monotonic.  This is a forwards-flow transfer-function computation.
  abstract public Type value();

  // Shortcut to update self-value.  Typically, used in contexts where it is NOT
  // locally monotonic - hence we cannot run any monotonicity asserts until the
  // invariant is restored over the entire region.
  public Type xval( ) {
    Type oval = _val;    // Get old type
    Type nval = value(); // Get best type
    if( nval!=oval ) {
      _val = nval;
      add_flow_uses(); // Put uses on worklist... values flows downhill
      deps_work_clear();
    }
    return nval;
  }

  // Shortcut for input value
  public Type val(int idx) { return in(idx)._val; }

  
  // --------------------------------------------------------------------------
  public Type _live;    // Liveness; assumed live in gvn.iter(), assumed dead in gvn.gcp().
  
  // Compute the current best liveness for this Node, based on the liveness of
  // its uses.  If basic_liveness(), returns a simple DEAD/ALIVE.  Otherwise,
  // computes the alive memory set down to the field level.  May return
  // TypeMem.FULL, especially if its uses are of unwired functions.
  // It must be monotonic.
  // This is a reverse-flow transfer-function computation.
  public Type live( ) {
    // Compute meet/union of all use livenesses
    Type live = Type.ANY;           // Start at lattice top
    for( Node use : _uses )         // Computed across all uses
      if( use._live != Type.ANY ) { // If use is alive, propagate liveness
        // The same def might be used on several inputs, with separate notions
        // of liveness
        for( int i=0; i<use.len(); i++ ) {
          if( use.in(i)==this ) {
            Type ulive = use.live_use(i);
            live = live.meet(ulive); // Make alive used fields
          }
        }
      }
    assert live==Type.ANY || live==Type.ALL || assert_live(live);
    return live;
  }

  // Shortcut to update self-live
  public void xliv( ) {
    Type oliv = _live;  // Get old live
    Type nliv = live(); // Get new live
    if( nliv!=oliv ) {
      _live = nliv;
      add_flow_defs();  // Put uses on worklist... live flows uphill
      deps_work_clear();
    }
  }
  // Compute local contribution of use liveness to this def.
  // Overridden in subclasses that do per-def liveness.
  Type live_use( int i ) { return _live; }
  boolean assert_live(Type live) { return isMem()==(live instanceof TypeMem tm && tm.flatten_live_fields()==tm); }

  // --------------------------------------------------------------------------
  // Hindley-Milner inspired typing, or CNC Thesis based congruence-class
  // typing.  This is a Type Variable which can unify with other TV3s forcing
  // Type-equivalence (JOIN of unified Types), and includes gross structure
  // (functions, structs, pointers, or simple Types).
  TV3 _tvar;
  
  // H-M Type-Variables
  public TV3 tvar() {
    TV3 tv = _tvar.find();                  // Do U-F step
    return tv == _tvar ? tv : (_tvar = tv); // Update U-F style in-place.
  }
  abstract public boolean has_tvar();
  public TV3 tvar(int x) { return in(x).tvar(); } // nth TV2
  // Initial set of type variables; lazy; handles cycles.
  public final TV3 set_tvar() {
    assert has_tvar();          // Sanity check
    if( _tvar!=null ) return tvar();
    TV3 tvar = _set_tvar();
    if( _tvar==tvar ) return tvar;
    assert _tvar==null; // Still a null: this is a recursive check that _tvar is not assigned twice
    return (_tvar=tvar);        // Assign and return
  }
  
  // Initial default compute of type variables.  No set, no smarts.  Overridden.
  TV3 _set_tvar() { return new TVLeaf(); }


  // Unifies this Node with others; Call/CallEpi with Fun/Parm/Ret.  NewNodes &
  // Load/Stores, etc.  Returns true if progressed, and puts neighbors back on
  // the worklist.  If work==null then make no changes, but return if progress
  // would be made.
  public boolean unify( boolean test ) { return false; }

  // Unify this Proj with the matching TV2 part from the multi-TV2-producing
  public boolean unify_proj( ProjNode proj, boolean test ) { throw TODO(); }
  
  // --------------------------------------------------------------------------

  // Dependents.  Changes to 'this' adds these to the worklist, and clears the list.
  Ary<Node> _deps;
  // Add a non-local dependent.
  void deps_add( Node dep ) {
    assert findDef(dep) == -1 && findUse(dep) == -1; // Non-local; local dependents already handled
    if( _deps==null ) _deps = new Ary<>(new Node[1],0);
    if( _deps.find(dep)==-1 && mid_work_assert()) {
      assert dep!=null;
      _deps.push(dep);
    }
  }
  
  // Add dependents to the flow & reduce lists, and clear the deps.
  public final void deps_work_clear() {
    if( _deps == null ) return;
    for( Node dep : _deps ) {
      GVN.add_flow_reduce(dep);
      if( dep instanceof FunNode fun ) GVN.add_inline(fun);
    }
    _deps.clear();
  }

  // --------------------------------------------------------------------------
  Node( Node... defs ) {
    _uid  = newuid();
    _defs = defs;  _len = defs.length;
    _uses = new Node[1]; _ulen = 0;
    _deps = null;
    _val  = _live = Type.ALL;
    _tvar = null;
  }

  // Make a copy of the base node, with no defs nor uses and a new UID.
  // Some variations will use the CallEpi for e.g. better error messages.
  @NotNull public Node copy( boolean copy_edges) {
    try {
      Node n = (Node)clone();
      n._uid = newuid();                  // A new UID
      n._defs = new Node[0]; n._len  = 0; // New empty uses
      n._uses = new Node[0]; n._ulen = 0; // New empty uses
      n._elock=false;           // Not in GVN
      n._tvar =null;
      if( copy_edges )
        for( int i=0; i<_len; i++ )
          n.addDef(_defs[i]);
      GVN.add_work_new(n);
      return n;
    } catch( CloneNotSupportedException cns ) { throw new RuntimeException(cns); }
  }

  // --------------------------------------------------------------------------

  // Initialize a Node, once input edges are completed.  Might have no users
  // (yet), so liveness is meaningless.  Cannot do HM TVs either, until the
  // program is complete.  Only sets value.
  public final <N extends Node> N init() { _val = value(); return (N)this; }
  
  // Graph rewriting.  Strictly reducing Nodes or Edges.  Cannot make a new
  // Node, save that for the expanding ideal calls.
  // Returns null if no-progress or a better version of 'this'.  The
  // transformed graph must remain monotonic in both value() and live().
  public Node ideal_reduce() { return null; }

  // Graph rewriting.  Keeps the same count of Nodes & Edges but might change
  // Edges or replace Nodes.  Returns null for no-progress.
  public Node ideal_mono() { return null; }

  // Graph rewriting.  General growing xforms are here, except for inlining.
  // Things like inserting MemSplit/MemJoin (which strictly increase graph
  // parallelism).  Returns null for no-progress.
  public Node ideal_grow() { return null; }
  
  public void add_flow_defs() { GVN.add_flow_defs(this); }
  public void add_flow_uses() { GVN.add_flow_uses(this); }
  //public Node add_flow     () { return GVN.add_flow(this); }
  //public void add_reduce_uses() { GVN.add_reduce_uses(this); }


  
  // Run peepholes are a recently parsed Node; Node has no uses (yet).
  // Node can be idealized and reduced to other Nodes.
  public final Node peep() {
    assert _val == null;        // Otherwise we need to check monotonic
    assert _ulen==0;            // No uses yet
    _val = value();
    
    if( shouldCon() )
      return kill(new ConNode(_val).peep());

    // Try CSE
    if( !_elock ) {             // Not in VALS and can still replace
      Node x = VALS.get(this);  // Try VALS
      if( x != null )           // Hit
        throw TODO(); //return merge(x);        // Graph replace with x
    }

    // Try general ideal call
    Node x = ideal_reduce();    // Try the general reduction
    if( x != null ) {
      assert _live.isa(x._live);
      return GVN.add_flow(x);   // Graph replace with x
    }

    return null;                // No change
  }

  // reducing xforms, strictly fewer Nodes or Edges.  n may be either in or out
  // of VALS.  If a replacement is found, replace.  In any case, put in the
  // VALS table.  Return null if no progress, or this or the replacement.
  public Node do_reduce() {
    //Node nnn = _do_reduce();
    //if( nnn!=null ) {           // Something happened
    //  add_flow_uses();          // Users of change should recheck
    //  if( nnn!=this ) {         // Replacement
    //    add_reduce_uses();      // New chances for V-N
    //    subsume(nnn);           // Replace
    //  }
    //  return nnn._elock();      // After putting in VALS
    //}
    //// No progress; put in VALS and return no-change
    //_elock();
    //return null;
    throw TODO();
  }


  //// Check for being not-live, being a constant, CSE in VALS table, and then
  //// call out to ideal_reduce.  Returns an equivalent replacement (or self).
  //private Node _do_reduce() {
  //  // Replace with a constant, if possible
  //  if( should_con(_val) )
  //    return merge(con(_val));
  //
  //  // Try CSE
  //  if( !_elock ) {             // Not in VALS and can still replace
  //    Node x = VALS.get(this);  // Try VALS
  //    if( x != null )           // Hit
  //      return merge(x);        // Graph replace with x
  //  }
  //
  //  // Try general ideal call
  //  Node x = ideal_reduce();    // Try the general reduction
  //  if( x != null ) {
  //    assert _live.isa(x._live);
  //    return x.add_flow();      // Graph replace with x
  //  }
  //
  //  return null;                // No change
  //}
  //
  //// At least as alive
  //private Node merge(Node x) {
  //  x._live = x._live.meet(_live);
  //  if( Combo.post() && tvar() != x.tvar() )
  //    tvar().unify(x.tvar(),false);
  //  return GVN.add_flow(x);
  //}

  // Change values at this Node directly.
  public Node do_flow() {
    Node progress=null;
    // Compute live bits.  If progressing, push the defs on the flow worklist.
    // This is a reverse flow computation.  Always assumed live if keep.
    Type oliv = _live;
    Type nliv = live();
    if( oliv != nliv ) {        // Progress?
      progress = this;          // Progress!
      assert nliv.isa(oliv);    // Monotonically improving
      _live = nliv;             // Record progress
      add_flow_defs();          // Classic reverse flow
      deps_work_clear();
    }

    // Compute best value.  If progressing, push uses on the flow worklist.
    // This is a forward flow computation.
    Type oval = _val;    // Get old type
    Type nval = value(); // Get best type
    if( nval!=oval ) {
      progress = this;          // Progress!
      assert nval.isa(oval);    // Monotonically improving
      _val = nval;
      add_flow_uses();          // Classic forwards flow
      deps_work_clear();
      //if( this instanceof CallNode call && CallNode.ttfp(oval)!=CallNode.ttfp(nval) ) {
      //  GVN.add_reduce(call);        // Can wire
      //  GVN.add_reduce(call.cepi()); // Can wire
      //}
      //if( nval.is_con() ) GVN.add_reduce(this); // Replace a constant
      //if( this instanceof RootNode ) add_flow();    // Rerun liveness
    }
    return progress;
  }

  public Node do_mono() {
    Node x = ideal_mono();
    if( x==null ) return null;
    assert x==this;
    return GVN.add_mono(GVN.add_flow_reduce(x));
  }

  public Node do_grow() {
    Node nnn = ideal_grow();
    if( nnn==null || nnn==this || isDead() ) return nnn;
    subsume(nnn);
    return GVN.add_flow_reduce(nnn);
  }

  // Replace with a ConNode iff
  // - Not already a ConNode AND
  // - Not an ErrNode AND
  // - Type.is_con()
  public boolean shouldCon() { return false; }
    //if( !t.is_con() || (t.above_center() && t!=TypeNil.NIL)) return false; // Not a constant
    //if( this instanceof ConNode    || // Already a constant
    //    this instanceof FunPtrNode || // Already a constant
    //    this instanceof NewNode    || // Can be a constant, but need the alias info
    //    this instanceof ErrNode    || // Never touch an ErrNode
    //    this instanceof AssertNode || // Never touch an AssertNode
    //    this instanceof FreshNode  || // These modify the TVars but not the constant flows
    //    (this instanceof StructNode st && !st.is_closed()) || // Struct is in-progress
    //    is_mem() ||
    //    is_prim() )                 // Never touch a Primitive
    //  return false; // Already a constant, or never touch an ErrNode
    //// External fidxs are never constants, except primitives which are both
    //// external and the same everywhere.
    //if( !is_prim() &&
    //    t instanceof TypeFunPtr tfp &&
    //    BitsFun.EXT.test_recur(tfp.fidx()) )
    //  return false;
    //return true;

  // Make globally shared common ConNode for this type.
  public static @NotNull Node con( Type t ) {
    //Node con = new ConNode<>(t);
    //Node con2 = VALS.get(con);
    //if( con2 != null ) {        // Found a prior constant
    //  if( Combo.HM_FREEZE && con2._tvar != con._tvar )
    //    throw TODO();
    //  con.kill();               // Kill the just-made one
    //  con = con2;
    //  con._live = Type.ALL;     // Adding more liveness
    //} else {                    // New constant
    //  con._val = t;             // Typed
    //  con._live = Combo.post() ? Type.ANY : Type.ALL;     // Not live yet
    //  if( Combo.post() && con.has_tvar() ) con.set_tvar();
    //  con._elock(); // Put in VALS, since if Con appears once, probably appears again in the same XFORM call
    //}
    //return GVN.add_flow(con); // Updated live flows
    throw TODO();
  }

  
  // --------------------------------------------------------------------------

  // Do One Step of forwards-dataflow analysis.  Assert monotonic progress.
  // If progressed, add neighbors on worklist.
  public void combo_forwards() {
    Type oval = _val;           // Old local type
    Type nval = value();        // New type
    if( oval == nval ) return;  // No progress
    assert oval.isa(nval);      // Monotonic
    _val = nval;                // Record progress
    add_flow_uses();            // Classic forwards flow on change.
    deps_work_clear();          // Any extra flow changes
  }

  // Do One Step of backwards-dataflow analysis.  Assert monotonic progress.
  // If progressed, add neighbors on worklist.
  public void combo_backwards() {
    Type oliv = _live;
    Type nliv = live();
    // TODO: If use._value >= constant, force live-use to ANY.
    // Not done for ITER, because replace-with constant happens anyways.
    if( oliv == nliv ) return;  // No progress
    assert oliv.isa(nliv);      // Monotonic
    _live = nliv;               // Record progress
    add_flow_defs();            // Classic reverse flow on change.
    deps_work_clear();          // Any extra flow changes
  }

  // Do One Step of Hindley-Milner unification.  Assert monotonic progress.
  // If progressed, add neighbors on worklist.
  public void combo_unify() {
    TV3 old = _tvar;
    if( old==null ) return;
    //if( _val == Type.ANY ) { /*tvar().deps_add_deep(this); */ return; } // No HM progress on untyped code
    // No HM progress on dead code, except for Call uses; required to unify calls.
    if( _live== Type.ANY && !has_call_use() ) 
      return;
    if( unify(false) ) {
      assert !_tvar.find().unify(old.find(),true);// monotonic: unifying with the result is no-progress
      TVExpanding.do_delay_fresh();
      // HM changes; push related neighbors
      for( Node def : _defs ) if( def!=null && def.has_tvar() ) GVN.add_flow(def);
      for( Node use : _uses ) if(              use.has_tvar() ) GVN.add_flow(use);
    }
  }

  // TODO: rethink this, or make virtual
  private boolean has_call_use() { return this instanceof FunPtrNode; }

  //// Node n is new in Combo (NOT GCP), cannot do most graph-reshape but
  //// commonly hit in VALS and this is OK.
  //public Node init1( ) {
  //  Node x = VALS.get(this);
  //  if( x!=null ) {             // Hit in GVN table
  //    kill();                   // Kill just-init'd
  //    return x;                 // Return old, which will add uses
  //  }
  //  _elock();                   // Install in GVN
  //  _val = _live = Type.ANY;    // Super optimistic types
  //  if( has_tvar() ) set_tvar();
  //  return GVN.add_flow(this);
  //}

  // --------------------------------------------------------------------------
  // Reset primitives.  Mostly unwire called and wired primitives.
  public final int walk_reset( int ignore ) {
    assert isPrim();           // Primitives
    _elock = false;             // Clear elock if reset_to_init0
    _deps = null;               // No deps
    if( _tvar!=null ) _tvar.reset_deps();
    walk_reset0();              // Special reset

    //// Remove non-prim inputs to a prim.  Skips all asserts and worklists.
    //Node c;
    //while( _defs._len>0 && (c=_defs.last())!=null && !c.is_prim() )
    //  _defs.pop()._uses.del(this);
    //// Remove non-prim uses of a prim.
    //for( int i=0; i<_uses._len; i++ )
    //  if( !(c = _uses.at(i)).is_prim() ) {
    //    while( c.len() > 0 ) {
    //      Node x = c._defs.pop();
    //      if( x!=null ) x._uses.del(c);
    //    }
    //    i--;
    //  }
    //return 0;
    throw TODO();
  }
  // Non-recursive specialized version
  void walk_reset0( ) {}

  // --------------------------------------------------------------------------
  // Assert all value and liveness calls only go forwards, and if they can
  // progress they are on the worklist.
  private static final VBitSet VISIT = new VBitSet();
  private static boolean MORE_WORK_ASSERT;
  public final int more_work( ) {
    assert !MORE_WORK_ASSERT;
    MORE_WORK_ASSERT = true;
    int rez = walk( Node::more_work );
    MORE_WORK_ASSERT = false;
    return rez;
  }
  public static boolean mid_work_assert() { return MORE_WORK_ASSERT; }
  private int more_work( int errs ) {
    if( GVN.on_dead(this) ) return -1; // Do not check dying nodes or reachable from dying
    if( isPrim() ) return errs;        // Do not check primitives
    // Check for GCP progress
    Type oval= _val, nval = value(); // Forwards flow
    Type oliv=_live, nliv = live (); // Backwards flow
    if( oval!=nval || oliv!=nliv ) {
      if( !(AA.LIFTING
            ? nval.isa(oval) && nliv.isa(oliv)
            : oval.isa(nval) && oliv.isa(nliv)) )
        errs += _report_bug("Monotonicity bug");
      if( !GVN.on_flow(this) && (AA.LIFTING || AA.DO_GCP) )
        errs += _report_bug("Progress bug");
    }
    // Check for HMT progress
    if( !AA.LIFTING &&                      // Falling, in Combo, so HM is running
        oliv!=Type.ANY && oval!=Type.ANY && // Alive in any way
        has_tvar() &&                       // Doing TVar things
        (!GVN.on_flow(this) || Combo.HM_FREEZE) ) { // Not already on worklist, or past freezing
      if( unify(true) )
        errs += _report_bug(Combo.HM_FREEZE ? "Progress after freezing" : "Progress bug");
    }
    return errs;
  }
  private int _report_bug(String msg) {
    VISIT.clear(_uid); // Pop-frame & re-run in debugger
    System.err.println(msg);
    System.err.println(NodePrinter.prettyPrint(this,0));
    // BREAKPOINT HERE
    VISIT.set(_uid); // Reset if progressing past breakpoint
    return 1;
  }

  // Assert all ideal, value and liveness calls are done
  private static final VBitSet IDEAL_VISIT = new VBitSet();
  public final boolean no_more_ideal() {
    assert !MORE_WORK_ASSERT;
    MORE_WORK_ASSERT = true;
    IDEAL_VISIT.clear();
    boolean no_more = !_more_ideal();
    MORE_WORK_ASSERT = false;
    return no_more;
  }
  private boolean _more_ideal() {
    if( IDEAL_VISIT.tset(_uid) ) return false; // Been there, done that
    if( !isKeep() && !GVN.on_dead(this)) { // Only non-keeps, which is just top-level scope and prims
      Node x;
      if( !GVN.on_reduce(this) ) { x = do_reduce(); if( x != null )
                                                         return true; } // Found an ideal call
      if( !GVN.on_mono  (this) ) { x = do_mono  (); if( x != null )
                                                         return true; } // Found an ideal call
      if( !GVN.on_grow  (this) ) { x = do_grow  (); if( x != null )
                                                         return true; } // Found an ideal call
      if( this instanceof FunNode fun && !GVN.on_inline(fun) && _must_inline==0 ) fun.ideal_inline(true);
    }
    for( Node def : _defs ) if( def != null && def._more_ideal() ) return true;
    for( Node use : _uses ) if( use != null && use._more_ideal() ) return true;
    return false;
  }


  // --------------------------------------------------------------------------
  // Gather errors, walking from Scope to START.
  public void walkerr_def( HashSet<ErrMsg> errs, VBitSet bs ) {
    if( bs.tset(_uid) ) return; // Been there, done that
    for( int i=0; i<_len; i++ ) {
      Node def = _defs[i];      // Walk data defs for more errors
      if( def == null || def._val == Type.XCTRL ) continue;
      // Walk function bodies that are wired
      if( def instanceof FunPtrNode && !(this instanceof RootNode) )
        continue;
      def.walkerr_def(errs,bs);
    }
    // Skip reporting if any input is 'all', as the input should report instead.
    for( int i=0; i<_len; i++ ) {
      Node def = _defs[i];      // Walk data defs for more errors
      if( def !=null && def._val ==Type.ALL )
        return;                 // Skip reporting.
    }
    adderr(errs);
  }

  private void adderr( HashSet<ErrMsg> errs ) {
    ErrMsg msg = err(false);
    if( msg==null ) return;
    msg._order = errs.size();
    errs.add(msg);
  }
  // Return any type error message, or null if no error
  public ErrMsg err( boolean fast ) { return null; }

  
  // --------------------------------------------------------------------------
  // Generic Visitor Pattern
  // Map takes and updates/reduces int x.
  // If map returns -1, the walk is stopped and x is not updated.
  public interface NodeMap { int map(Node n, int x); }
  final public int walk( NodeMap map ) {
    assert VISIT.isEmpty();
    int rez = _walk(map,0);
    VISIT.clear();
    return rez;
  }
  
  private int _walk( NodeMap map, int x ) {
    if( VISIT.tset(_uid) ) return x; // Been there, done that
    int x2 = map.map(this,x);
    if( x2 == -1 ) return x;
    for( Node def : _defs )  if( def != null )  x2 = def._walk(map,x2);
    for( Node use : _uses )                     x2 = use._walk(map,x2);
    return x2;
  }

  // --------------------------------------------------------------------------
  
  // Easy assertion check
  boolean check_solo_mem_writer(Node memw) {
    boolean found=false;
    for( Node use : _uses )
      if( use == memw ) found=true; // Only memw mem-writer follows
      else if( use.isMem()  ) return false; // Found a 2nd mem-writer
      else if( use.isKeep() ) return false; // Being built, might see a store-use yet
    return found;
  }

  // Shortcut
  public Type sharptr( Node mem ) { return mem._val.sharptr(_val); }

  //// Walk a subset of the dominator tree, looking for the last place (highest
  //// in tree) this predicate passes, or null if it never does.
  //Node walk_dom_last(Predicate<Node> P) {
  //  assert in(0) != null;       // All default control nodes pass ctrl in slot 0
  //  Node n = in(0).walk_dom_last(P);
  //  if( n != null ) return n;   // Take last answer first
  //  return P.test(this) ? this : null;
  //}

}
