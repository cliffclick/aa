package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.HashSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntSupplier;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.node.FunNode._must_inline;

// Sea-of-Nodes
public abstract class Node implements Cloneable, IntSupplier {
  static final byte OP_BINDFP = 1;
  static final byte OP_CALL   = 2;
  static final byte OP_CALLEPI= 3;
  static final byte OP_CAST   = 4;
  static final byte OP_CON    = 5;
  static final byte OP_CONTYPE= 6;
  static final byte OP_CPROJ  = 7;
  static final byte OP_ERR    = 8;
  static final byte OP_FRESH  = 9;
  static final byte OP_FP2DSP =10;
  static final byte OP_FREF   =11;
  static final byte OP_FUN    =12;
  static final byte OP_FUNPTR =13;
  static final byte OP_IF     =14;
  static final byte OP_JOIN   =15;
  static final byte OP_KEEP   =16;
  static final byte OP_LOAD   =17;
  static final byte OP_NEW    =18; // Allocate a new struct
  static final byte OP_PARM   =19;
  static final byte OP_PHI    =20;
  static final byte OP_PRIM   =21;
  static final byte OP_PROJ   =22;
  static final byte OP_REGION =23;
  static final byte OP_RET    =24;
  static final byte OP_ROOT   =25;
  static final byte OP_SCOPE  =26;
  static final byte OP_SPLIT  =27;
  static final byte OP_STORE  =28;
  static final byte OP_STRUCT =29;
  static final byte OP_TYPE   =30;
  static final byte OP_VAL    =31;
  static final byte OP_MAX    =32;

  private static final String[] STRS = new String[] { null, "BindFP", "Call", "CallEpi", "Cast", "Con", "ConType", "CProj", "Err", "Fresh", "FP2DSP", "ForwardRef", "Fun", "FunPtr", "If", "Join", "Keep", "Load", "New", "Parm", "Phi", "Prim", "Proj", "Region", "Return", "Root", "Scope","Split", "Store", "Struct", "Type", "Val" };
  static { assert STRS.length==OP_MAX; }

  // Unique dense node-numbering
  private static int CNT=1; // Do not hand out UID 0
  int newuid() {
    assert CNT < 100000 : "infinite node create loop";
    if( CNT==AA.UID )
      System.out.print("");     // Handy break-at-UID
    return CNT++;
  }
  @Override public int getAsInt() { return _uid; }


  public static int _INIT0_CNT = 99999;
  // Initial state after loading e.g. primitives.
  public static void init0() { _INIT0_CNT=CNT; }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  public static void reset_to_init0() { CNT = _INIT0_CNT; }

  // Is a primitive
  public boolean always_prim() { return _uid<_INIT0_CNT; }
  public boolean is_prim() { return _uid<_INIT0_CNT && PrimNode.post_init(); }

  public int _uid;      // Unique ID, will have gaps, used to give a dense numbering to nodes
  public final byte _op;// Opcode (besides the object class), used to avoid v-calls in some places
  public boolean _elock;// Edge-lock: cannot modify edges because messes up hashCode & GVN
  public Type _val;     // Value; starts at ALL and lifts towards ANY.
  public Type _live;    // Liveness; assumed live in gvn.iter(), assumed dead in gvn.gcp().
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
  // Initial compute of type variables.  No set, no smarts.  Overridden.
  TV3 _set_tvar() { return new TVLeaf(); }

  // Hash is function+inputs, or opcode+input_uids, and is invariant over edge
  // order (so we can swap edges without rehashing)
  @Override public int hashCode() {
    int sum = _op;
    for( int i=0; i<_defs._len; i++ ) if( _defs._es[i] != null ) sum ^= _defs._es[i]._uid;
    return sum;
  }
  // Equals is function+inputs, or opcode+input_uids.  Uses pointer-equality
  // checks for input equality checks.
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof Node n) ) return false;
    if( _op != n._op ) return false;
    if( n._defs==null || _defs._len != n._defs._len ) return false;
    // Note pointer-equality
    for( int i=0; i<_defs._len; i++ ) if( _defs._es[i] != n._defs._es[i] ) return false;
    return true;
  }

  // Defs.  Generally fixed length, ordered, nulls allowed, no unused trailing space.  Zero is Control.
  public Ary<Node> _defs;
  public int len() { return _defs._len; }
  public Node in( int i) { return _defs.at(i); }
  // Edge lock check, or anything that changes the hash
  public void unelock() {
    assert check_vals();        // elock & VALs match
    if( _elock ) {              // Edge-locked
      _elock=false;             // Unlock
      Node x = VALS.remove(this);
      assert x==this;           // Got the right node out
    }
  }
  public Node _elock() {        // No assert version, used for new nodes
    assert check_vals();        // elock & VALs match
    if( !_elock && VALS.get(this)==null ) { _elock = true; VALS.put(this,this); }
    return this;
  }

  static long NANO=0;
  public boolean check_vals( ) {
    return true; // VERY EXPENSIVE ASSERT
//    Node x = VALS.get(this), old=null;
//    if( x == this ) old=this;   // Found in table quickly
//    // Hunt the hard way
//    else {
//      long t = System.nanoTime();
//      for( Node o : VALS.keySet() ) if( o._uid == _uid ) { old=o; break; }
//      NANO += System.nanoTime()-t;
//    }
//    return (old!=null) == _elock;
  }

  // Add def/use edge
  public Node add_def(Node n) { unelock(); _defs.add(n); if( n!=null ) n._uses.add(this); return this; }
  // Replace def/use edge
  public Node set_def( int idx, Node n ) {
    unelock();
    Node old = _defs.at(idx);  // Get old value
    // Add edge to new guy before deleting old, in case old goes dead and
    // recursively makes new guy go dead also
    if( (_defs._es[idx] = n) != null ) n._uses.add(this);
    return unuse(old);
  }

  public void replace(Node old, Node nnn) { unelock(); _defs.replace(old,nnn); }

  public Node insert (int idx, Node n) { unelock(); _defs.insert(idx,n); if( n!=null ) n._uses.add(this); return this; }
  // Return Node at idx, withOUT auto-deleting it, even if this is the last
  // use.  Used by the parser to retrieve final Nodes from tmp holders.  Does
  // NOT preserve order.
  public Node del( int idx ) {
    unelock();
    Node n = _defs.del(idx);
    if( n != null ) n._uses.del(this);
    return n;
  }
  public Node pop( ) { unelock(); Node n = _defs.pop(); unuse(n); return n; }
  // Remove Node at idx, auto-delete and preserve order.
  public Node remove(int idx) { unelock(); return unuse(_defs.remove(idx)); }
  // Remove Node, auto-delete and preserve order.  Error if not found
  public Node remove(Node x) { return remove(_defs.find(x)); }

  private Node unuse( Node old ) {
    if( old == null ) return this;
    old._uses.del(this);
    // Either last use of old & goes dead, or at least 1 fewer uses & changes liveness
    Env.GVN.add_unuse(old);
    return this;
  }

  // Replace, but do not delete this.  Really used to insert a node in front of
  // this.  Does graph-structure changes, making pointers-to-this point to nnn.
  // Changes neither 'this' nor 'nnn'.  Does not enforce any monotonicity nor
  // unification.
  public void insert( Node nnn ) {
    if( _uses._len>0 ) unelock(); // Hacking edges
    while( _uses._len > 0 ) {
      Node u = _uses.del(0);  // Old use
      u.replace(this,nnn);    // was this now nnn
      nnn._uses.add(u);
    }
  }

  // Complete replacement; point uses to 'nnn' and removes 'this'.
  public void subsume( Node nnn ) {
    assert !nnn.is_dead();
    insert(nnn);                // Change graph shape
    kill();                     // Delete the old, and anything it uses
  }

  // Kill a node; all inputs are null'd out; this may put more dead Nodes on
  // the dead worklist.  Return this for progress, null for no-progress.
  public Node kill( ) {
    assert !is_prim();
    if( is_dead() ) return null;
    assert _uses._len==0;
    deps_work_clear();          // Put dependents on worklist
    // Similar to unelock(), except do not put on any worklist
    if( _elock ) { _elock = false; Node x = VALS.remove(this); assert x == this; }
    while( _defs._len > 0 ) unuse(_defs.pop());
    _defs = _uses = null;       // TODO: Poor-man's indication of a dead node, probably needs to recycle these...
    return this;
  }
  public boolean is_dead() { return _uses == null; }

  // Keep a Node alive during all optimizations, because future direct uses
  // will yet appear.  The Node can otherwise be fully optimized and replaced
  // with equivalents.  The push/pop sequences are strongly asserted for stack
  // order.
  public int push() { return GVNGCM.push(this); }
  public static Node pop (int idx) { assert idx==GVNGCM.KEEP_ALIVE._defs._len;  return GVNGCM.pop(idx); }
  public static Node peek(int idx) { assert idx<=GVNGCM.KEEP_ALIVE._defs._len;  return GVNGCM.KEEP_ALIVE.in(idx-1); }
  public static void pops(int nargs) { for( int i=0; i<nargs; i++ ) GVNGCM.KEEP_ALIVE.pop(); }
  public boolean is_keep() {
    for( Node use : _uses ) if( use instanceof KeepNode )  return true;
    return false;
  }

  // Uses.  Generally variable length; unordered, no nulls, compressed, unused trailing space
  public Ary<Node> _uses;

  // Dependents.  Changes to 'this' adds these to the worklist, and clears the list.
  Ary<Node> _deps;
  // Add a dep
  void deps_add(Node dep) {
    if( _deps==null ) _deps = new Ary<>(new Node[1],0);
    if( _deps.find(dep)==-1 && VISIT.isEmpty() /*no progress during bulk testing*/) {
      assert dep!=null;
      _deps.push(dep);
    }
  }
  // Reset deps list to mark (deps added during this idealizing do not count).
  // Add other deps to the flow & reduce lists, and clear the deps.
  public final void deps_work_clear() {
    if( _deps == null ) return;
    for( Node dep : _deps ) {
      Env.GVN.add_reduce(dep.add_flow());
      if( dep instanceof FunNode fun ) Env.GVN.add_inline(fun);
    }
    _deps.clear();
  }

  Node( byte op ) { this(op,new Node[0]); }
  Node( byte op, Node... defs ) {
    _op   = op;
    _uid  = newuid();
    _defs = new Ary<>(defs);
    _uses = new Ary<>(new Node[1],0);
    _deps = null;
    for( Node def : defs ) if( def != null ) def._uses.add(this);
    _val  = _live = Type.ALL;
    _tvar = null;
  }

  // Make a copy of the base node, with no defs nor uses and a new UID.
  // Some variations will use the CallEpi for e.g. better error messages.
  @NotNull public Node copy( boolean copy_edges) {
    try {
      Node n = (Node)clone();
      n._uid = newuid();                  // A new UID
      n._defs = new Ary<>(new Node[1],0); // New empty defs
      n._uses = new Ary<>(new Node[1],0); // New empty uses
      n._elock=false;           // Not in GVN
      if( copy_edges )
        for( Node def : _defs )
          n.add_def(def);
      Env.GVN.add_work_new(n);
      return n;
    } catch( CloneNotSupportedException cns ) { throw new RuntimeException(cns); }
  }

  // Short string name
  public String xstr() { return STRS[_op]; } // Self short name
  String  str() { return xstr(); }    // Inline longer name
  @Override public String toString() { return dump(0,new SB(),null, null, null, null, false,false).toString(); }
  // Dump
  public String dump( int max ) { return dump(max,is_prim(),false,false); }
  // Dump including primitives
  public String dump( int max, boolean prims, boolean plive, boolean ptvar ) { return dump(0,max,new VBitSet(), new SB(),null, null, null, null,prims,plive,ptvar).toString();  }
  // Dump one node, no recursion
  private SB dump( int d, SB sb, VBitSet typebs, NonBlockingHashMapLong dups, VBitSet hmt_bs, VBitSet hmt_dups, boolean plive, boolean ptvar ) {
    String xs = String.format("%s%4d: %-7.7s ",plive ? _live : "",_uid,xstr());
    sb.i(d).p(xs);
    if( is_dead() ) return sb.p("DEAD");
    for( Node n : _defs ) sb.p(n == null ? "____ " : String.format("%4d ",n._uid));
    sb.p(" [[");
    for( Node n : _uses ) sb.p(String.format("%4d ",n._uid));
    sb.p("]]  ");
    sb.p(str()).s();
    if( _val==null ) sb.p("----");
    else _val.str(sb, typebs, dups, true, false); // Print a type using the shared dups printer
    if( ptvar && _tvar!=null ) _tvar.str(sb.p(" - "), hmt_bs, hmt_dups, true, false);

    return sb;
  }
  // Dump one node IF not already dumped, no recursion
  private void dump(int d, VBitSet bs, SB sb, VBitSet typebs, NonBlockingHashMapLong dups, VBitSet hmt_bs, VBitSet hmt_dups, boolean plive, boolean ptvar ) {
    if( bs.tset(_uid) ) return;
    dump(d,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar).nl();
  }
  // Recursively print, up to depth
  private SB dump( int d, int max, VBitSet bs, SB sb, VBitSet typebs, NonBlockingHashMapLong<String> dups, VBitSet hmt_bs, VBitSet hmt_dups, boolean prims, boolean plive, boolean ptvar ) {
    if( bs.tset(_uid) ) return sb;
    if( d < max ) {    // Limit at depth
      // Print parser scopes first (deepest)
      for( Node n : _defs ) if( n instanceof ScopeNode ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
      // Print constants early
      for( Node n : _defs ) if( n instanceof ConNode ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
      // Do not recursively print root Scope, nor primitives.
      // These are too common, and uninteresting.
      for( Node n : _defs ) if( n != null && (!prims && n.is_prim() && n._defs._len > 3) ) bs.set(n._uid);
      // Recursively print most of the rest, just not the multi-node combos and
      // Unresolve & FunPtrs.
      for( Node n : _defs )
        if( n != null && !n.is_multi_head() && !n.is_multi_tail() && !(n instanceof FunPtrNode) )
          n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
      // Print FunPtrs, which typically catch whole functions.
      for( Node n : _defs )
        if( n instanceof FunPtrNode )
          n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
      // Print anything not yet printed, including multi-node combos
      for( Node n : _defs ) if( n != null && !n.is_multi_head() ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
      for( Node n : _defs ) if( n != null ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
    }
    // Print multi-node combos all-at-once, including all tails even if they
    // exceed the depth limit by 1.
    Node x = is_multi_tail() ? in(0) : this;
    if( x != null && x.is_multi_head() ) {
      int dx = d+(x==this?0:1);
      // Print all tails paths, all at once - nothing recursively below the tail
      for( Node n : x._uses )
        if( n.is_multi_tail() )
          for( Node m : n._defs )
            if( dx<max) m.dump(dx+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
      if( x==this ) bs.clear(_uid); // Reset for self, so prints right now
      x.dump(dx,bs,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar); // Conditionally print head of combo
      // Print all combo tails, if not already printed
      if( x!=this ) bs.clear(_uid); // Reset for self, so prints in the mix below
      for( Node n : x._uses ) if( n.is_multi_tail() ) n.dump(dx-1,bs,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar);
      return sb;
    } else { // Neither combo head nor tail, just print
      return dump(d,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar).nl();
    }
  }
  public boolean is_multi_head() { return _op==OP_CALL || _op==OP_CALLEPI || _op==OP_FUN || _op==OP_IF || _op==OP_NEW || _op==OP_REGION || _op==OP_SPLIT || _op==OP_ROOT; }
  private boolean is_multi_tail() { return _op==OP_PARM || _op==OP_PHI || _op==OP_PROJ || _op==OP_CPROJ; }
  boolean is_CFG() { return false; }

  public String dumprpo( boolean prims, boolean plive, boolean ptvar ) {
    Ary<Node> nodes = new Ary<>(new Node[1],0);
    postorder(nodes,new VBitSet());
    // Walk the node list and count Type duplicates.  This means the same types
    // use the same Dup name on every node in the entire print.
    NonBlockingHashMapLong<String> dups = new NonBlockingHashMapLong<>();
    VBitSet typebs = new VBitSet();
    Type.UCnt ucnt = new Type.UCnt();
    VBitSet hmt_bs   = new VBitSet();
    VBitSet hmt_dups = new VBitSet();
    for( Node n : nodes ) {
      n._val ._str_dups(typebs, dups, ucnt, false);
      n._live._str_dups(typebs, dups, ucnt, false);
      if( n._tvar!=null ) n._tvar._get_dups(hmt_bs,hmt_dups,true,prims);
    }
    typebs.clr();
    hmt_bs.clr();

    // Dump in reverse post order
    SB sb = new SB();
    Node prior = null;
    for( int i=nodes._len-1; i>=0; i-- ) {
      Node n = nodes.at(i);
      if( n.is_prim() && !prims )
        continue;               // Visited, but do not print
      // Add a nl after the last of a multi-tail sequence.
      if( (prior != null && prior.is_multi_tail() && !n.is_multi_tail()) ||
          // Add a nl before the start of a multi-head sequence.
          n.is_multi_head() )
        sb.nl();
      if( n._op==OP_FUN ) _header((FunNode)n,sb);
      n.dump(0,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar).nl();
      if( n._op==OP_RET && n.in(4) instanceof FunNode ) _header((FunNode)n.in(4),sb);
      prior = n;
    }
    return sb.toString();
  }
  private static void _header(FunNode fun, SB sb) {
    sb.p("============ ").p(fun==null?"null":fun.name()).p(" ============").nl();
  }
  private void postorder( Ary<Node> nodes, VBitSet bs ) {
    if( bs.tset(_uid) ) return;
    // If CFG, walk the CFG first.  Do not walk thru Returns (into Calls) as
    // this breaks up the whole- functions-at-once.
    if( is_CFG() && _op!=OP_RET && is_copy(0)==null ) {
      // Walk any CProj first.
      for( Node use : _uses )
        if( use._op == OP_CPROJ )
          use.postorder(nodes,bs);
      // Walk the CFG, walking CallEpis last
      for( Node use : _uses )
        if( !(use instanceof CallEpiNode) && use.is_CFG() )
          use.postorder(nodes,bs);
      for( Node use : _uses )
        if(  (use instanceof CallEpiNode) && use.is_CFG() )
          use.postorder(nodes,bs);
    }

    // Walk the rest (especially data).  Since visit bits are set on the CFGs
    // its OK to walk them also.  Calls are special, since their Proj's feed
    // into a Fun's Parms.  We want the Fun to walk its own Parms, in order so
    // ignore these edges.  Since the Parms are all reachable from the Fun they
    // get walked eventually.
    if( (_op != OP_CALL || is_copy(0)!=null ) && _op!=OP_RET ) {
      if( _op!=OP_SPLIT || _uses._len!=2 ) {
        for( Node use : _uses )
          use.postorder(nodes,bs);
      }  else {                 // For MemSplit, walk the "busy" side first
        Node p0 = _uses.at(0), p1 = _uses.at(1);
        if( ((ProjNode)p0)._idx==1 ) { p0=p1; p1=_uses.at(0); } // Swap
        p1.postorder(nodes,bs);
        p0.postorder(nodes,bs);
      }
    }

    // Slight PO tweak: heads and tails together.
    if( is_multi_head() )
      for( Node use : _uses )
        if( use.is_multi_tail() )
          nodes.push(use);
    if( !is_multi_tail() ) nodes.push(this);
  }

  // Utility during debugging to find a reachable Node by _uid
  public  Node find( int uid ) { return find(uid,new VBitSet()); }
  private Node find( int uid, VBitSet bs ) {
    if( _uid==uid ) return this;
    if( bs.tset(_uid) || is_dead() ) return null;
    Node m;
    for( Node n : _defs ) if( n!=null && (m=n.find(uid,bs)) !=null ) return m;
    for( Node n : _uses ) if(            (m=n.find(uid,bs)) !=null ) return m;
    return null;
  }

  // Initialize a Node in GVN.
  public final <N extends Node> N init() { return (N)Env.GVN.init(this); }


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

  public Type val(int idx) { return in(idx)._val; }

  // Compute the current best liveness for this Node, based on the liveness of
  // its uses.  If basic_liveness(), returns a simple DEAD/ALIVE.  Otherwise,
  // computes the alive memory set down to the field level.  May return
  // TypeMem.FULL, especially if its uses are of unwired functions.
  // It must be monotonic.
  // This is a reverse-flow transfer-function computation.
  public Type live( ) { return live(true); }
  Type live( boolean all ) {
    // Compute meet/union of all use livenesses
    Type live = Type.ANY;           // Start at lattice top
    for( Node use : _uses )         // Computed across all uses
      if( use._live != Type.ANY ) { // If use is alive, propagate liveness
        // The same def might be used on several inputs, with separate notions
        // of liveness
        for( int i=0; i<use.len(); i++ ) {
          if( use.in(i)==this && (all || use.is_mem()) ) {
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
  boolean assert_live(Type live) { return is_mem()==(live instanceof TypeMem tm && tm.flatten_live_fields()==tm); }

  public void add_flow_defs() { Env.GVN.add_flow_defs(this); }
  public void add_flow_uses() { Env.GVN.add_flow_uses(this); }
  public Node add_flow     () { return Env.GVN.add_flow(this); }
  public void add_reduce_uses() { Env.GVN.add_reduce_uses(this); }

  // Unifies this Node with others; Call/CallEpi with Fun/Parm/Ret.  NewNodes &
  // Load/Stores, etc.  Returns true if progressed, and puts neighbors back on
  // the worklist.  If work==null then make no changes, but return if progress
  // would be made.
  public boolean unify( boolean test ) { return false; }

  // Unify this Proj with the matching TV2 part from the multi-TV2-producing
  public boolean unify_proj( ProjNode proj, boolean test ) { throw unimpl(); }

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
    if( _val == Type.ANY ) { /*tvar().deps_add_deep(this); */ return; } // No HM progress on untyped code
    // No HM progress on dead code, except for Call uses; required to unify calls.
    if( _live== Type.ANY && !has_call_use() ) 
      return;
    if( unify(false) ) {
      assert !_tvar.find().unify(old.find(),true);// monotonic: unifying with the result is no-progress
      TVExpanding.do_delay_fresh();
      TVExpanding.do_delay_resolve();
      // HM changes; push related neighbors
      for( Node def : _defs ) if( def!=null && def.has_tvar() ) def.add_flow();
      for( Node use : _uses ) if(              use.has_tvar() ) use.add_flow();
    }
  }
  private boolean has_call_use() { return this instanceof FunPtrNode; }

  // Return any type error message, or null if no error
  public ErrMsg err( boolean fast ) { return null; }

  // Global expressions, to remove redundant Nodes
  public static final ConcurrentHashMap<Node,Node> VALS = new ConcurrentHashMap<>();

  // Reducing xforms, strictly fewer Nodes or Edges.  n may be either in or out
  // of VALS.  If a replacement is found, replace.  In any case, put in the
  // VALS table.  Return null if no progress, or this or the replacement.
  public Node do_reduce() {
    assert check_vals();
    Node nnn = _do_reduce();
    if( nnn!=null ) {           // Something happened
      add_flow_uses();          // Users of change should recheck
      if( nnn!=this ) {         // Replacement
        add_reduce_uses();      // New chances for V-N
        subsume(nnn);           // Replace
      }
      return nnn._elock();      // After putting in VALS
    }
    // No progress; put in VALS and return no-change
    _elock();
    return null;
  }

  // Check for being not-live, being a constant, CSE in VALS table, and then
  // call out to ideal_reduce.  Returns an equivalent replacement (or self).
  private Node _do_reduce() {
    // Replace with a constant, if possible
    if( should_con(_val) )
      return merge(con(_val));

    // Try CSE
    if( !_elock ) {             // Not in VALS and can still replace
      Node x = VALS.get(this);  // Try VALS
      if( x != null )           // Hit
        return merge(x);        // Graph replace with x
    }

    // Try general ideal call
    Node x = ideal_reduce();    // Try the general reduction
    if( x != null ) {
      assert _live.isa(x._live);
      return x.add_flow();      // Graph replace with x
    }

    return null;                // No change
  }

  // Fold control copies
  Node fold_ccopy() {
    Node cc = in(0).is_copy(0);
    if( cc==null ) return null;
    if( cc==this ) return Env.ANY;
    add_reduce_uses();
    return Env.GVN.add_reduce(set_def(0,cc));
  }

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
      if( this instanceof CallNode call && CallNode.ttfp(oval)!=CallNode.ttfp(nval) ) {
        Env.GVN.add_reduce(call);        // Can wire
        Env.GVN.add_reduce(call.cepi()); // Can wire
      }
      if( nval.is_con() ) Env.GVN.add_reduce(this); // Replace a constant
      if( this instanceof RootNode ) add_flow();    // Rerun liveness
    }
    return progress;
  }

  public Node do_mono() {
    Node x = ideal_mono();
    if( x==null ) return null;
    assert x==this;
    return Env.GVN.add_mono(Env.GVN.add_reduce(x.add_flow()));
  }

  public Node do_grow() {
    Node nnn = ideal_grow();
    if( nnn==null || nnn==this || is_dead() ) return nnn;
    subsume(nnn);
    return Env.GVN.add_reduce(nnn.add_flow());
  }

  // Replace with a ConNode iff
  // - Not already a ConNode AND
  // - Not an ErrNode AND
  // - Type.is_con()
  public boolean should_con(Type t) {
    if( !t.is_con() || t.above_center() ) return false; // Not a constant
    if( this instanceof ConNode    || // Already a constant
        this instanceof FunPtrNode || // Already a constant
        this instanceof NewNode    || // Can be a constant, but need the alias info
        this instanceof ErrNode    || // Never touch an ErrNode
        this instanceof AssertNode || // Never touch an AssertNode
        this instanceof FreshNode  || // These modify the TVars but not the constant flows
        (this instanceof StructNode st && !st.is_closed()) || // Struct is in-progress
        is_mem() ||
        is_prim() )                 // Never touch a Primitive
      return false; // Already a constant, or never touch an ErrNode
    // External fidxs are never constants, except primitives which are both
    // external and the same everywhere.
    if( !is_prim() &&
        t instanceof TypeFunPtr tfp &&
        BitsFun.EXT.test_recur(tfp.fidx()) )
      return false;
    return true;
  }

  // Make globally shared common ConNode for this type.
  public static @NotNull Node con( Type t ) {
    if( t instanceof TypeFunPtr tfp && tfp.is_fidx() && tfp.fidx()!=BitsFun.ALLX )
      return RetNode.get(tfp.fidx()).funptr();
    Node con = new ConNode<>(t);
    Node con2 = VALS.get(con);
    if( con2 != null ) {        // Found a prior constant
      if( Combo.HM_FREEZE && con2._tvar != con._tvar )
        throw unimpl();
      con.kill();               // Kill the just-made one
      con = con2;
      con._live = Type.ALL;     // Adding more liveness
    } else {                    // New constant
      con._val = t;             // Typed
      con._live = Combo.post() ? Type.ANY : Type.ALL;     // Not live yet
      if( Combo.post() && con.has_tvar() ) con.set_tvar();
      con._elock(); // Put in VALS, since if Con appears once, probably appears again in the same XFORM call
    }
    return Env.GVN.add_flow(con); // Updated live flows
  }

  // Reset primitives.  Mostly unwire called and wired primitives.
  public final int walk_reset( int ignore ) {
    assert is_prim();           // Primitives
    _elock = false;             // Clear elock if reset_to_init0
    _deps = null;               // No deps
    if( _tvar!=null ) _tvar.reset_deps();
    walk_reset0();              // Special reset

    // Remove non-prim inputs to a prim.  Skips all asserts and worklists.
    Node c;
    while( _defs._len>0 && (c=_defs.last())!=null && !c.is_prim() )
      _defs.pop()._uses.del(this);
    // Remove non-prim uses of a prim.
    for( int i=0; i<_uses._len; i++ )
      if( !(c = _uses.at(i)).is_prim() ) {
        while( c.len() > 0 ) {
          Node x = c._defs.pop();
          if( x!=null ) x._uses.del(c);
        }
        i--;
      }
    return 0;
  }
  // Non-recursive specialized version
  void walk_reset0( ) {}

  // At least as alive
  private Node merge(Node x) {
    x._live = x._live.meet(_live);
    return Env.GVN.add_flow(x);
  }

  // Node n is new in Combo (NOT GCP), cannot do most graph-reshape but
  // commonly hit in VALS and this is OK.
  public Node init1( ) {
    Node x = VALS.get(this);
    if( x!=null ) {             // Hit in GVN table
      kill();                   // Kill just-init'd
      return x;                 // Return old, which will add uses
    }
    _elock();                   // Install in GVN
    _val = _live = Type.ANY;    // Super optimistic types
    if( has_tvar() ) set_tvar();
    return Env.GVN.add_flow(this);
  }

  // --------------------------------------------------------------------------
  // Assert all value and liveness calls only go forwards, and if they can
  // progress they are on the worklist.
  private static boolean MORE_WORK_ASSERT;
  public final int more_work( ) {
    MORE_WORK_ASSERT = true;
    int rez = walk( Node::more_work );
    MORE_WORK_ASSERT = false;
    return rez;
  }
  public static boolean mid_work_assert() { return MORE_WORK_ASSERT; }
  private int more_work( int errs ) {
    if( Env.GVN.on_dead(this) ) return -1; // Do not check dying nodes or reachable from dying
    if( is_prim() ) return errs;           // Do not check primitives
    // Check for GCP progress
    Type oval= _val, nval = value(); // Forwards flow
    Type oliv=_live, nliv = live (); // Backwards flow
    if( oval!=nval || oliv!=nliv ) {
      if( !(AA.LIFTING
            ? nval.isa(oval) && nliv.isa(oliv)
            : oval.isa(nval) && oliv.isa(nliv)) )
        errs += _report_bug("Monotonicity bug");
      if( !Env.GVN.on_flow(this) && (AA.LIFTING || AA.DO_GCP) )
        errs += _report_bug("Progress bug");
    }
    // Check for HMT progress
    if( !AA.LIFTING &&                      // Falling, in Combo, so HM is running
        oliv!=Type.ANY && oval!=Type.ANY && // Alive in any way
        has_tvar() &&                       // Doing TVar things
        (!Env.GVN.on_flow(this) || Combo.HM_FREEZE) ) { // Not already on worklist, or past freezing
      if( unify(true) )
        errs += _report_bug(Combo.HM_FREEZE ? "Progress after freezing" : "Progress bug");
    }
    return errs;
  }
  private int _report_bug(String msg) {
    VISIT.clear(_uid); // Pop-frame & re-run in debugger
    System.err.println(msg);
    System.err.println(dump(0,new SB(),null,null,null,null,true,false)); // Rolling backwards not allowed
    VISIT.set(_uid); // Reset if progressing past breakpoint
    return 1;
  }

  // Assert all ideal, value and liveness calls are done
  private static final VBitSet IDEAL_VISIT = new VBitSet();
  public final boolean no_more_ideal() {
    IDEAL_VISIT.clear();
    return !_more_ideal();
  }
  private boolean _more_ideal() {
    if( IDEAL_VISIT.tset(_uid) ) return false; // Been there, done that
    if( !is_keep() && !Env.GVN.on_dead(this)) { // Only non-keeps, which is just top-level scope and prims
      Node x;
      if( !Env.GVN.on_reduce(this) ) { x = do_reduce(); if( x != null )
                                                         return true; } // Found an ideal call
      if( !Env.GVN.on_mono  (this) ) { x = do_mono  (); if( x != null )
                                                         return true; } // Found an ideal call
      if( !Env.GVN.on_grow  (this) ) { x = do_grow  (); if( x != null )
                                                         return true; } // Found an ideal call
      if( this instanceof FunNode fun && !Env.GVN.on_inline(fun) && _must_inline==0 ) fun.ideal_inline(true);
    }
    for( Node def : _defs ) if( def != null && def._more_ideal() ) return true;
    for( Node use : _uses ) if( use != null && use._more_ideal() ) return true;
    return false;
  }


  // --------------------------------------------------------------------------
  // Gather errors, walking from Scope to START.
  public void walkerr_def( HashSet<ErrMsg> errs, VBitSet bs ) {
    if( bs.tset(_uid) ) return; // Been there, done that
    for( int i=0; i<_defs._len; i++ ) {
      Node def = _defs.at(i);   // Walk data defs for more errors
      if( def == null || def._val == Type.XCTRL ) continue;
      // Walk function bodies that are wired
      if( def instanceof FunPtrNode && !(this instanceof RootNode) )
        continue;
      def.walkerr_def(errs,bs);
    }
    // Skip reporting if any input is 'all', as the input should report instead.
    for( Node def : _defs )
      if( def !=null && def._val ==Type.ALL )
        return;                 // Skip reporting.
    adderr(errs);
  }

  private void adderr( HashSet<ErrMsg> errs ) {
    ErrMsg msg = err(false);
    if( msg==null ) return;
    msg._order = errs.size();
    errs.add(msg);
  }

  // --------------------------------------------------------------------------
  // Generic Visitor Pattern
  static private final VBitSet VISIT = new VBitSet();
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
  // Overridden in subclasses that return TypeTuple value types.  Such nodes
  // are always followed by ProjNodes to break out the tuple slices.  If the
  // node optimizes, each ProjNode becomes a copy of some other value... based
  // on the ProjNode index
  public Node is_copy(int idx) { return null; }

  // Only true for Unresolved
  public boolean is_forward_ref() { return false; }
  // Only true for a bare ProjNode
  public boolean is_forward_type() { return false; }

  // True if normally (not in-error) produces a TypeMem value or a TypeTuple
  // with a TypeMem at(MEM_IDX).
  public boolean is_mem() { return false; }
  // Easy assertion check
  boolean check_solo_mem_writer(Node memw) {
    boolean found=false;
    for( Node use : _uses )
      if( use == memw ) found=true; // Only memw mem-writer follows
      else if( use.is_mem() ) return false; // Found a 2nd mem-writer
      else if( use instanceof KeepNode ) return false; // Being built, might see a store-use yet
    return found;
  }

  // Shortcut
  public Type sharptr( Node mem ) { return mem._val.sharptr(_val); }

  // Aliases that a MemJoin might choose between.  Not valid for nodes which do
  // not manipulate memory.
  //BitsAlias escapees() { throw unimpl("graph error"); }

  // Walk a subset of the dominator tree, looking for the last place (highest
  // in tree) this predicate passes, or null if it never does.
  Node walk_dom_last(Predicate<Node> P) {
    assert in(0) != null;       // All default control nodes pass ctrl in slot 0
    Node n = in(0).walk_dom_last(P);
    if( n != null ) return n;   // Take last answer first
    return P.test(this) ? this : null;
  }

}
