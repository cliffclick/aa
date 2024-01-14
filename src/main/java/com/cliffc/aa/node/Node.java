package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVExpanding;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.util.*;

import java.util.Arrays;
import java.util.HashSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntSupplier;

import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.Env.GVN;

// Sea-of-Nodes
@SuppressWarnings("unchecked")
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
    for( int i=0; i< _len; i++ ) if( (m=_defs[i])!=null && (m=m.find(uid,bs)) !=null ) return m;
    for( int i=0; i<_ulen; i++ ) if( (m=_uses[i])!=null && (m=m.find(uid,bs)) !=null ) return m;
    return null;
  }

  
  public static int _PRIM_CNT = 99999;
  // Initial state after loading e.g. primitives.
  public static void initPrim() { _PRIM_CNT=CNT; }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  public static void reset_to_init0() { CNT = _PRIM_CNT; }

  // Is a primitive
  public boolean isPrim() { return Env.NODE_LO <= _uid && _uid < _PRIM_CNT; }
  // Keep all the early nodes for repeated testing
  public boolean isResetKeep() { return _uid < _PRIM_CNT; }

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
  // Phis, Parms, Projs
  public boolean isMultiTail() { return false; }
  
  // Region, Fun, If, Return, Call, CallEpi
  public boolean isCFG() { return false; }

  // --------------------------------------------------------------------------
  // Node pretty-print info

  // String label; interned; unique per node class, but might be more refined
  // than just class name.  E.g. "Add" or "Phi_Mem" or "Call_foo"
  abstract String label();

  // Debugger Printing.
    
  // {@code toString} is what you get in the debugger.  It has to print 1
  // line (because this is what a debugger typically displays by default) and
  // has to be robust with broken graph/nodes.
  @Override public final String toString() {  return _printLine(new SB(),false).toString(); }

  // Print a node on 1 line, columnar aligned, as:
  // NNID NNAME DDEF DDEF  [[  UUSE UUSE  ]]  TYPE
  // 1234 sssss 1234 1234 1234 1234 1234 1234 tttttt
  public final SB _printLine( SB sb, boolean live ) {
    if( live ) {
      String slive = _live.toString();
      sb.p("%-20.20s ".formatted(slive));
    }
    sb.p("%4d %-7.7s ".formatted(_uid,label()));
    if( isDead() ) return sb.p("DEAD\n");
    for( int i=0; i<_len; i++ ) {
      Node def = _defs[i];
      sb.p(def==null ? "____ " : "%4d ".formatted(def._uid));
    }
    for( int i = _len; i<3; i++ ) sb.p("     ");
    sb.p(" [[  ");
    for( int i=0; i<_ulen; i++ ) {
      Node use = _uses[i];
      sb.p(use==null ? "____ " : "%4d ".formatted(use._uid));
    }
    int lim = 6 - Math.max(_len,4);
    for( int i = _ulen; i<lim; i++ )
      sb.p("     ");
    sb.p(" ]]  ");
    if( _val!= null ) _val.str(sb,true,false);
    return sb.p("\n");
  }

  String p(int d) { return NodePrinter.prettyPrint(this,d,isPrim()); }
  

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
      int len = 32 - Integer.numberOfLeadingZeros(_len)+1;
      while( len <= _len ) len<<=1;
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
  public Node use(int idx) { assert idx < _ulen; return _uses[idx]; }
  // Add a use, making more space as needed.
  private void _addUse( Node n ) {
    // A NPE here means the _uses are null, which means the Node was killed
    if( _ulen == _uses.length ) {
      int len = 1<<(32-Integer.numberOfLeadingZeros(_ulen));
      while( len <= _ulen ) len<<=1;
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
    for( int i=_ulen-1; i>=0; i-- )  if( _uses[i]==use )  return i;
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
      _hash=0;                  // Recompute hash going back
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

  // Delete def by index, preserving edges but not order.
  // Kills if going dead
  void del( int idx ) {
    unelock();
    Node n = _defs[idx];
    _defs[idx] = _defs[--_len];
    _unuse(n);
  }

  // Remove last def, and attempt to kill
  public void pop( ) { del(_len-1); }

  // Remove last def and return it, no kill.
  public Node popKeep( ) {
    unelock();
    Node n = _defs[--_len];
    if( n != null ) n._delUse(this);
    return n;
  }
  
  // Delete 1st instanceof named def; error if not found.
  // Does not preserve order.
  public void del( Node def ) { del(findDef(def)); }

  
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

  // Already nuked the {this->old} edge, now nuke the {old->this} edge and
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
    if( n!=null ) n.keep();
    kill();
    return n==null ? null : n.unkeep();
  }

  // Hash is function+inputs, or opcode+input_uids, and is invariant over edge
  // order (so we can swap edges without rehashing)
  private int _hash;
  @Override public final int hashCode() {
    if( _hash!=0 ) return _hash;
    int sum = label().hashCode() + hash();
    for( Node def : defs() ) if( def != null ) sum ^= def._uid;
    if( sum==0 ) sum = 0xDEADBEEF;
    return (_hash=sum);
  }
  int hash() { return 0; }      // Override this
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
    boolean isMem = isMem();
    for( int j=0; j<nUses(); j++ ) {       // Computed across all uses
      Node use = use(j);
      if( use==null )
        return isMem ? TypeMem.ALLMEM : Type.ALL; // Keep-alive, so fully alive
      if( use._live != Type.ANY ) { // If use is alive, propagate liveness
        // The same def might be used on several inputs, with separate notions
        // of liveness
        for( int i=0; i<use.len(); i++ ) {
          if( use.in(i)==this ) {
            Type ulive = use.live_use(i);
            // Things like CProj or DProj are either all/not alive.  If
            // 'this.isMem', e.g. a Call or CallEpi, the Projs keep the node
            // alive but do not add any memory refinements.
            if( isMem && ulive==Type.ALL ) ulive = TypeMem.ANYMEM;
            live = live.meet(ulive); // Make alive used fields
          }
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
  Node setLive(Type live) { _live=live; return this; }
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
    if( _deps.find(dep)==-1 && NodeUtil.mid_work_assert()) {
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
    for( Node def : defs() ) if( def != null ) def._addUse(this);
    _uses = new Node[1]; _ulen = 0;
    _deps = null;
    _val  = _live = Type.ALL;
    _tvar = null;
  }

  // Make a copy of the base node, with no defs nor uses and a new UID.
  // Some variations will use the CallEpi for e.g. better error messages.
  public Node copy( boolean copy_edges) {
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
  public final <N extends Node> N init() { _val = value(); GVN.add_flow_reduce(this); return (N)this; }
  
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
  private boolean _peeped;      // One-shot assert only
  public final Node peep() {
    assert !_peeped;
    _peeped = true;
    Type old = _val;
    _val = value();
    assert _val.isa(old);  // Monotonic
    assert _ulen==0;       // No uses yet, so can use what is returned directly
    Node x = _do_reduce(); // Find a reduced version, if any
    return x==null ? this : kill(x);  // Always return a not-null
  }

  // Compute a new replacement for 'this' that is generally "better" -
  // uses a constant or an existing node or is somehow reduced.
  // Returns null if no-progress.
  private Node _do_reduce() {
    if( shouldCon() )
      return kill(new ConNode(_val).setLive(_live).peep());

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
    Node nnn = _do_reduce();
    if( nnn!=null ) {           // Something happened
      GVN.add_flow_uses(this);  // Users of change should recheck value
      GVN.add_flow_defs(this);  // Defs  of change should recheck liveness
      if( nnn!=this ) {         // Replacement
        GVN.add_reduce_uses(this); // New chances for V-N
        subsume(nnn);           // Replace
      }
      return nnn._elock();      // Put progress in VALs and return change
    }
    // No progress; put in VALS and return no-change
    _elock();
    return null;
  }

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
  public boolean shouldCon() {
    return !isPrim() && _val.is_con();
  }
    //    this instanceof NewNode    || // Can be a constant, but need the alias info
    //    this instanceof ErrNode    || // Never touch an ErrNode
    //    this instanceof AssertNode || // Never touch an AssertNode
    //    this instanceof FreshNode  || // These modify the TVars but not the constant flows
    //    is_mem() ||
    //  return false; // Already a constant, or never touch an ErrNode
    //return true;

  // Make globally shared common ConNode for this type.
  public static Node con( Type t ) {
    return new ConNode<>(t).peep();
  }

  
  // --------------------------------------------------------------------------

  // Do One Step of forwards-dataflow analysis.  Assert monotonic progress.
  // If progressed, add neighbors on worklist.
  public void combo_forwards() {
    if( isPrim() ) return;
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
    if( isPrim() ) return;
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
      for( Node def : defs() ) if( def!=null && def.has_tvar() ) GVN.add_flow(def);
      for( Node use : uses() ) if(              use.has_tvar() ) GVN.add_flow(use);
    }
  }

  // TODO: rethink this, or make virtual
  private boolean has_call_use() { return this instanceof FunPtrNode; }

  // --------------------------------------------------------------------------
  // Reset primitives.  Mostly unwire called and wired primitives.
  public final void walk_reset( ) {
    if( !isResetKeep() ) return;   // Primitives
    _elock = false;             // Clear elock if reset_to_init0
    _deps = null;               // No deps
    if( _tvar!=null ) _tvar.reset_deps();
    walk_reset0();              // Special reset

    // Remove non-prim inputs to a prim.  Skips all asserts and worklists.
    Node c;
    while( _len>0 && (c=last())!=null && !c.isResetKeep()) {
      _len--;
      c._delUse(this);
    }
    // Remove non-prim uses of a prim.
    for( int i=0; i<_ulen; i++ )
      if( (c = _uses[i]) != null && !c.isResetKeep() ) {
        while( c._len-- > 0 ) {
          Node x = c._defs[c._len];
          if( x!=null ) x._delUse(c);
        }
        i--;
      }
    if( isPrim() )
      _live = isMem() ? TypeMem.ALLMEM : Type.ALL;
    return;
  }
  // Non-recursive specialized version
  void walk_reset0( ) {}


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

  public interface NodeMap { void map(Node n); }
  final public void walk( NodeMap map ) {
    assert WVISIT.isEmpty();
    _walk(map);
    WVISIT.clear();
  }
  
  private void _walk( NodeMap map ) {
    if( WVISIT.tset(_uid) ) return; // Been there, done that
    map.map(this);
    for( Node def : defs() )  if( def != null )  def._walk(map);
    for( Node use : uses() )  if( use != null )  use._walk(map);
  }

  // Map takes and updates/reduces int x.
  // If map returns -1, the walk is stopped and x is not updated.
  static final VBitSet WVISIT = new VBitSet();
  public interface NodeMapR { int map(Node n, int x); }
  final public int walkReduce( NodeMapR map ) {
    assert WVISIT.isEmpty();
    int rez = _walkR(map,0);
    WVISIT.clear();
    return rez;
  }
  
  private int _walkR( NodeMapR map, int x ) {
    if( WVISIT.tset(_uid) ) return x; // Been there, done that
    int x2 = map.map(this,x);
    if( x2 == -1 ) return x;
    for( Node def : defs() )  if( def != null )  x2 = def._walkR(map,x2);
    for( Node use : uses() )  if( use != null )  x2 = use._walkR(map,x2);
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

}
