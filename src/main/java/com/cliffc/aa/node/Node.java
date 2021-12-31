package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.HashSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntSupplier;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;

// Sea-of-Nodes
public abstract class Node implements Cloneable, IntSupplier {
  static final byte OP_CALL   = 1;
  static final byte OP_CALLEPI= 2;
  static final byte OP_CAST   = 3;
  static final byte OP_CON    = 4;
  static final byte OP_CONTYPE= 5;
  static final byte OP_CPROJ  = 6;
  static final byte OP_ERR    = 7;
  static final byte OP_FRESH  = 8;
  static final byte OP_FUN    = 9;
  static final byte OP_FUNPTR =10;
  static final byte OP_IF     =11;
  static final byte OP_JOIN   =12;
  static final byte OP_KEEP   =13;
  static final byte OP_LOAD   =14;
  static final byte OP_LOOP   =15;
  static final byte OP_NAME   =16; // Cast a prior NewObj to have a runtime Name
  static final byte OP_NEWOBJ =17; // Allocate a new struct
  static final byte OP_NEWARY =18; // Allocate a new array
  static final byte OP_NEWSTR =19; // Allocate a new string
  static final byte OP_PARM   =20;
  static final byte OP_PHI    =21;
  static final byte OP_PRIM   =22;
  static final byte OP_PROJ   =23;
  static final byte OP_REGION =24;
  static final byte OP_RET    =25;
  static final byte OP_SCOPE  =26;
  static final byte OP_SPLIT  =27;
  static final byte OP_START  =28;
  static final byte OP_STMEM  =29;
  static final byte OP_STORE  =30;
  static final byte OP_TYPE   =31;
  static final byte OP_UNR    =32;
  static final byte OP_VAL    =33;
  static final byte OP_MAX    =34;

  private static final String[] STRS = new String[] { null, "Call", "CallEpi", "Cast", "Con", "ConType", "CProj", "Err", "Fresh", "Fun", "FunPtr", "If", "Join", "Keep", "Load", "Loop", "Name", "NewObj", "NewAry", "NewStr", "Parm", "Phi", "Prim", "Proj", "Region", "Return", "Scope","Split", "Start", "StartMem", "Store", "Type", "Unresolved", "Val" };
  static { assert STRS.length==OP_MAX; }

  // Unique dense node-numbering
  public  static int _INIT0_CNT;
  private static int CNT=1; // Do not hand out UID 0
  int newuid() {
    assert CNT < 100000 : "infinite node create loop";
    if( CNT==AA.UID )
      System.out.print("");
    return CNT++;
  }
  @Override public int getAsInt() { return _uid; }

  // Initial state after loading e.g. primitives.
  public static void init0() {
    _INIT0_CNT=CNT;
  }
  // Reset is called after a top-level exec exits (e.g. junits) with no parse
  // state left alive.  NOT called after a line in the REPL or a user-call to
  // "eval" as user state carries on.
  public static void reset_to_init0() {
    CNT = _INIT0_CNT;
  }


  public int _uid;      // Unique ID, will have gaps, used to give a dense numbering to nodes
  final byte _op;       // Opcode (besides the object class), used to avoid v-calls in some places
  public boolean _elock;// Edge-lock: cannot modify edges because messes up hashCode & GVN
  public Type _val;     // Value; starts at ALL and lifts towards ANY.
  public TypeMem _live; // Liveness; assumed live in gvn.iter(), assumed dead in gvn.gcp().
  // Hindley-Milner inspired typing, or CNC Thesis based congruence-class
  // typing.  This is a Type Variable which can unify with other TV2s forcing
  // Type-equivalence (JOIN of unified Types), and includes gross structure
  // (functions, structs, pointers, or simple Types).
  TV2 _tvar;
  // H-M Type-Variables
  public TV2 tvar() {
    TV2 tv = _tvar.find();     // Do U-F step
    return tv == _tvar ? tv : (_tvar = tv); // Update U-F style in-place.
  }
  public boolean has_tvar() { return _tvar!=null; }
  public TV2 tvar(int x) { return in(x).tvar(); } // nth TV2
  public TV2 new_tvar(String alloc_site) { return TV2.make_leaf(this,alloc_site); }

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
    if( !(o instanceof Node) ) return false;
    Node n = (Node)o;
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
      Env.GVN.add_reduce(Env.GVN.add_flow(this));
    }
  }
  Node _elock() {               // No assert version, used for new nodes
    assert check_vals();        // elock & VALs match
    if( !_elock && VALS.get(this)==null ) { _elock = true; VALS.put(this,this); }
    return this;
  }

  public boolean check_vals( ) {
    Node x = VALS.get(this), old=null;
    if( x == this ) old=this;   // Found in table quickly
    // Hunt the hard way
    else for( Node o : VALS.keySet() ) if( o._uid == _uid ) { old=o; break; }
    return (old!=null) == _elock;
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
  public void del( int idx ) {
    unelock();
    Node n = _defs.del(idx);
    if( n != null ) n._uses.del(this);
  }
  public Node pop( ) { unelock(); Node n = _defs.pop(); unuse(n); return n; }
  // Remove Node at idx, auto-delete and preserve order.
  public Node remove(int idx) { unelock(); return unuse(_defs.remove(idx)); }

  private Node unuse( Node old ) {
    if( old == null ) return this;
    old._uses.del(this);
    // Either last use of old & goes dead, or at least 1 fewer uses & changes liveness
    Env.GVN.add_unuse(old);
    if( old._uses._len!=0 ) old.add_flow_def_extra(this);
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
    if( is_dead() ) return null;
    assert _uses._len==0;
    // Similar to unelock(), except do not put on any worklist
    if( _elock ) { _elock = false; Node x = VALS.remove(this); assert x == this; }
    while( _defs._len > 0 ) unuse(_defs.pop());
    _defs = _uses = null;       // TODO: Poor-man's indication of a dead node, probably needs to recycle these...
    if( this instanceof NewNode ) ((NewNode)this).free();
    return this;
  }
  public boolean is_dead() { return _uses == null; }

  // "keep" a Node during all optimizations because it is somehow unfinished.
  // Typically, used when needing to build several Nodes before building the
  // typically using Node; during construction the earlier Nodes have no users
  // (yet) and are not dead.  Acts "as if" there is an unknown user.
  public <N extends Node> N keep() { throw unimpl(); }
  public <N extends Node> N keep(int d) { throw unimpl(); }
  // Remove the keep flag, but do not delete.
  public <N extends Node> N unkeep() { throw unimpl(); }
  public <N extends Node> N unkeep(int d) { throw unimpl(); }
  // Remove the keep flag, and immediately allow optimizations.
  public <N extends Node> N unhook() { throw unimpl(); }

  // Keep a Node alive during all optimizations, because future direct uses
  // will yet appear.  The Node can otherwise be fully optimized and replaced
  // with equivalents.  The push/pop sequences are strongly asserted for stack
  // order.
  public int push() { GVNGCM.KEEP_ALIVE.add_def(this); return GVNGCM.KEEP_ALIVE._defs._len-1; }
  public static Node pop (int idx) { assert idx==GVNGCM.KEEP_ALIVE._defs._len-1;  return GVNGCM.KEEP_ALIVE.pop(); }
  public static Node peek(int idx) { assert idx<GVNGCM.KEEP_ALIVE._defs._len;  return GVNGCM.KEEP_ALIVE.in(idx); }
  public static void pops(int nargs) { for( int i=0; i<nargs; i++ ) GVNGCM.KEEP_ALIVE.pop(); }
  public boolean is_keep() {
    for( Node use : _uses ) if( use instanceof KeepNode )  return true;
    return false;
  }

  // Uses.  Generally variable length; unordered, no nulls, compressed, unused trailing space
  public Ary<Node> _uses;

  Node( byte op ) { this(op,new Node[0]); }
  Node( byte op, Node... defs ) {
    _op   = op;
    _uid  = newuid();
    _defs = new Ary<>(defs);
    _uses = new Ary<>(new Node[1],0);
    for( Node def : defs ) if( def != null ) def._uses.add(this);
    _val  = Type.ALL;
    _live = all_live();
    _tvar = null;
  }

  // Is a primitive
  public boolean is_prim() { return _INIT0_CNT==0 || _uid<_INIT0_CNT; }

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
  @Override public String toString() { return dump(0,new SB(),false).toString(); }
  // Dump
  public String dump( int max ) { return dump(max,is_prim(),false); }
  // Dump including primitives
  public String dump( int max, boolean prims, boolean plive ) { return dump(0, new SB(),max,new VBitSet(),prims,plive).toString();  }
  // Dump one node, no recursion
  private SB dump( int d, SB sb, boolean plive ) {
    String xs = String.format("%s%4d: %-7.7s ",plive ? _live : "",_uid,xstr());
    sb.i(d).p(xs);
    if( is_dead() ) return sb.p("DEAD");
    for( Node n : _defs ) sb.p(n == null ? "____ " : String.format("%4d ",n._uid));
    sb.p(" [[");
    for( Node n : _uses ) sb.p(String.format("%4d ",n._uid));
    sb.p("]]  ");
    sb.p(str()).s();
    if( _val==null ) sb.p("----");
    else _val.str(sb,new VBitSet(),null,true);

    return sb;
  }
  // Dump one node IF not already dumped, no recursion
  private void dump(int d, SB sb, VBitSet bs, boolean plive) {
    if( bs.tset(_uid) ) return;
    dump(d,sb,plive).nl();
  }
  // Recursively print, up to depth
  private SB dump( int d, SB sb, int max, VBitSet bs, boolean prims, boolean plive ) {
    if( bs.tset(_uid) ) return sb;
    if( d < max ) {    // Limit at depth
      // Print parser scopes first (deepest)
      for( Node n : _defs ) if( n instanceof ScopeNode ) n.dump(d+1,sb,max,bs,prims,plive);
      // Print constants early
      for( Node n : _defs ) if( n instanceof ConNode ) n.dump(d+1,sb,max,bs,prims,plive);
      // Do not recursively print root Scope, nor Unresolved of primitives.
      // These are too common, and uninteresting.
      for( Node n : _defs ) if( n != null && (!prims && n.is_prim() && n._defs._len > 3) ) bs.set(n._uid);
      // Recursively print most of the rest, just not the multi-node combos and
      // Unresolve & FunPtrs.
      for( Node n : _defs )
        if( n != null && !n.is_multi_head() && !n.is_multi_tail() &&
            !(n instanceof UnresolvedNode) && !(n instanceof FunPtrNode) )
          n.dump(d+1,sb,max,bs,prims,plive);
      // Print Unresolved and FunPtrs, which typically catch whole functions.
      for( Node n : _defs )
        if( (n instanceof UnresolvedNode) || (n instanceof FunPtrNode) )
          n.dump(d+1,sb,max,bs,prims,plive);
      // Print anything not yet printed, including multi-node combos
      for( Node n : _defs ) if( n != null && !n.is_multi_head() ) n.dump(d+1,sb,max,bs,prims,plive);
      for( Node n : _defs ) if( n != null ) n.dump(d+1,sb,max,bs,prims,plive);
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
            if( dx<max) m.dump(dx+1,sb,max,bs,prims,plive);
      if( x==this ) bs.clear(_uid); // Reset for self, so prints right now
      x.dump(dx,sb,bs,plive); // Conditionally print head of combo
      // Print all combo tails, if not already printed
      if( x!=this ) bs.clear(_uid); // Reset for self, so prints in the mix below
      for( Node n : x._uses ) if( n.is_multi_tail() ) n.dump(dx-1,sb,bs,plive);
      return sb;
    } else { // Neither combo head nor tail, just print
      return dump(d,sb,plive).nl();
    }
  }
  public boolean is_multi_head() { return _op==OP_CALL || _op==OP_CALLEPI || _op==OP_FUN || _op==OP_IF || _op==OP_LOOP || _op==OP_NEWOBJ || _op==OP_NEWSTR || _op==OP_REGION || _op==OP_SPLIT || _op==OP_START; }
  private boolean is_multi_tail() { return _op==OP_PARM || _op==OP_PHI || _op==OP_PROJ || _op==OP_CPROJ; }
  boolean is_CFG() { return _op==OP_CALL || _op==OP_CALLEPI || _op==OP_FUN || _op==OP_RET || _op==OP_IF || _op==OP_LOOP || _op==OP_REGION || _op==OP_START || _op==OP_CPROJ || _op==OP_SCOPE; }

  public String dumprpo( boolean prims, boolean plive ) {
    Ary<Node> nodes = new Ary<>(new Node[1],0);
    postorder(nodes,new VBitSet());
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
      n.dump(0,sb,plive).nl();
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
    if( is_CFG() && _op!=OP_RET ) {
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
    if( _op != OP_CALL && _op!=OP_RET ) {
      if( _op!=OP_SPLIT || _uses._len!=2 )
        for( Node use : _uses )
          use.postorder(nodes,bs);
      else {                    // For MemSplit, walk the "busy" side first
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
      Env.GVN.add_flow_uses(this); // Put uses on worklist... values flows downhill
      if( !may_be_con_live(oval) && may_be_con_live(nval) )
        Env.GVN.add_flow_defs(this); // If computing a constant
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
  public TypeMem live( ) {
    // Compute meet/union of all use livenesses
    TypeMem live = TypeMem.DEAD; // Start at lattice top
    for( Node use : _uses )      // Computed across all uses
      if( use.live_uses() ) {
        TypeMem ulive = use.live_use(this);
        live = (TypeMem)live.meet(ulive); // Make alive used fields
      }
    assert live==TypeMem.DEAD || live.basic_live()==all_live().basic_live();
    return live;
  }
  public boolean live_uses() {
    return _live != TypeMem.DEAD &&    // Only live uses make more live
      (!_live.basic_live() ||   // Complex alive always counts
       !may_be_con_live(_val) ||// Use might be replaced with a constant (and not have this input)
       is_prim() ||             // Always live prims
       err(true)!=null);        // Always live errors
  }

  // True if 't' may_be_con AND is not a TypeFunPtr.  If a Node computes a
  // constant, it can be replaced with a constant Node and all inputs go dead
  // and the corresponding ConNode gets flagged live.  However, this messes
  // with Nodes computing a constant TypeFunPtr, since it allows the entire
  // function to go dead.  Easy fix: disallow for TypeFunPtr.  Hard (better)
  // fix: make the corresponding FunPtrNode go alive.
  static boolean may_be_con_live(Type t) {
    //return t.may_be_con() &&      // Use might be replaced with a constant (and not have this input)
    //  !(t instanceof TypeFunPtr); // Always compute FunPtrs, as constants they keep function bodies alive
    return false;
  }

  // Shortcut to update self-live
  public Node xliv( ) { throw unimpl(); }
  // Compute local contribution of use liveness to this def.
  // Overridden in subclasses that do per-def liveness.
  public TypeMem live_use( Node def ) { return _live; }

  // Default lower-bound liveness.  For control, its always "ALIVE" and for
  // memory opts (and tuples with memory) its "ALLMEM".
  public TypeMem all_live() { return TypeMem.ALIVE; }

  // The _val changed here, and more than the immediate neighbors might change value/live
  public void add_flow_defs() { Env.GVN.add_flow_defs(this); }
  public void add_flow_extra(Type old) { }
  public void add_flow_use_extra(Node chg) { }
  public void add_flow_def_extra(Node chg) { }
  // Inputs changed here, and more than the immediate neighbors might reduce
  public void add_reduce_extra() { }

  // Unifies this Node with others; Call/CallEpi with Fun/Parm/Ret.  NewNodes &
  // Load/Stores, etc.  Returns true if progressed, and puts neighbors back on
  // the worklist.  If work==null then make no changes, but return if progress
  // would be made.
  public boolean unify( boolean test ) { return false; }

  // HM changes; push related neighbors
  public void add_work_hm() { tvar().add_deps_flow(); }

  // Do One Step of forwards-dataflow analysis.  Assert monotonic progress.
  // If progressed, add neighbors on worklist.
  public void combo_forwards() {
    Type oval = _val;           // Old local type
    Type nval = value();        // New type
    if( oval == nval ) return;  // No progress
    //assert nval==nval.simple_ptr(); // Only simple pointers in node types
    assert oval.isa(nval);      // Monotonic
    _val = nval;                // Record progress

    // Classic forwards flow on change.  Also wire Call Graph edges.
    for( Node use : _uses ) {
      Env.GVN.add_flow(use).add_flow_use_extra(this);
      if( use instanceof CallEpiNode ) ((CallEpiNode)use).check_and_wire(true);
      if( use instanceof   ScopeNode ) ((  ScopeNode)use).check_and_wire();
    }
    add_flow_extra(oval);
    if( this instanceof CallEpiNode ) ((CallEpiNode)this).check_and_wire(true);
    // All liveness is skipped if may_be_con, since the possible constant has
    // no inputs.  If values drop from being possible constants to not being a
    // constant, liveness must be revisited.
    //assert may_be_con_live(oval) || !may_be_con_live(nval); // May_be_con_live is monotonic
    //if( may_be_con_live(oval) && !may_be_con_live(nval) )
    //  for( Node def : _defs ) work.add(def); // Now check liveness
  }

  // Do One Step of backwards-dataflow analysis.  Assert monotonic progress.
  // If progressed, add neighbors on worklist.
  public void combo_backwards() {
    TypeMem oliv = _live;
    TypeMem nliv = live();
    if( oliv == nliv ) return;  // No progress
    assert oliv.isa(nliv);      // Monotonic
    _live = nliv;               // Record progress
    add_flow_extra(oliv);
    for( Node def : _defs )     // Classic reverse flow on change
      if( def!=null ) Env.GVN.add_flow(def).add_flow_def_extra(this);
  }

  // Do One Step of Hindley-Milner unification.  Assert monotonic progress.
  // If progressed, add neighbors on worklist.
  public void combo_unify() {
    if( _live==TypeMem.DEAD )  return; // No HM progress on dead code
    if( _val == Type.ANY ) return;     // No HM progress on untyped code
    TV2 old = _tvar==null ? null : tvar();
    if( old!=null && old.is_err() ) return;  // No unifications with error
    if( unify(false) ) {
      assert old==null || !_tvar.debug_find().unify(old.debug_find(),true);// monotonic: unifying with the result is no-progress
      add_work_hm();            // Neighbors on worklist
    }
  }

  // See if we can resolve an unresolved Call during the Combined algorithm
  public void combo_resolve(WorkNode ambi) { }

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
    if( nnn!=null ) {                   // Something happened
      if( nnn!=this ) {                 // Replacement
        Env.GVN.add_flow_uses(this);    // Visit users
        add_reduce_extra();
        subsume(nnn);                   // Replace
        for( Node use : nnn._uses ) {
          use.add_reduce_extra();
          use.add_flow_use_extra(nnn);
        }
      }
      Env.GVN.add_reduce(nnn);  // Rerun the replacement
      return nnn._elock();      // After putting in VALS
    }
    // No progress; put in VALS and return
    _elock();
    return null;
  }

  // Check for being not-live, being a constant, CSE in VALS table, and then
  // call out to ideal_reduce.  Returns an equivalent replacement (or self).
  private Node _do_reduce() {
    // Replace with a constant, if possible
    if( should_con(_val) )
      return con(_val);

    // Try CSE
    if( !_elock ) {             // Not in VALS and can still replace
      Node x = VALS.get(this);  // Try VALS
      if( x != null )           // Hit
        return merge(x);        // Graph replace with x
    }

    // Try general ideal call
    Node x = ideal_reduce();    // Try the general reduction
    if( x != null )
      return merge(x);          // Graph replace with x

    return null;                // No change
  }


  // Change values at this Node directly.
  public Node do_flow() {
    Node progress=null;
    // Compute live bits.  If progressing, push the defs on the flow worklist.
    // This is a reverse flow computation.  Always assumed live if keep.
    TypeMem oliv = _live;
    TypeMem nliv = live();
    if( oliv != nliv ) {        // Progress?
      progress = this;          // Progress!
      assert nliv.isa(oliv);    // Monotonically improving
      _live = nliv;             // Record progress
      for( Node def : _defs )   // Put defs on worklist... liveness flows uphill
        if( def != null ) Env.GVN.add_flow(def).add_flow_def_extra(this);
      add_flow_extra(oliv);
    }

    // Compute best value.  If progressing, push uses on the flow worklist.
    // This is a forward flow computation.
    Type oval = _val; // Get old type
    Type nval = value();// Get best type
    if( nval!=oval ) {
      progress = this;          // Progress!
      assert nval.isa(oval);    // Monotonically improving
      _val = nval;
      // If becoming a constant, check for replacing with a ConNode
      if( !may_be_con_live(oval) && may_be_con_live(nval) ) {
        Env.GVN.add_reduce(this);
        Env.GVN.add_flow_defs(this); // Since a constant, inputs are no longer live
      }
      // Put uses on worklist... values flows downhill
      for( Node use : _uses )
        Env.GVN.add_flow(use).add_flow_use_extra(this);
      // Progressing on CFG can mean CFG paths go dead
      if( is_CFG() ) for( Node use : _uses ) if( use.is_CFG() ) Env.GVN.add_reduce(use);
      add_flow_extra(oval);
    }
    return progress;
  }

  public Node do_mono() {
    Node x= ideal_mono();
    if( x==null ) return null;
    assert x==this;
    return Env.GVN.add_mono(Env.GVN.add_flow(Env.GVN.add_reduce(x)));
  }

  public Node do_grow() {
    Node nnn = ideal_grow();
    if( nnn==null || nnn==this || is_dead() ) return nnn;
    return Env.GVN.add_flow(Env.GVN.add_reduce(nnn));
  }

  // Replace with a ConNode iff
  // - Not already a ConNode AND
  // - Not an ErrNode AND
  // - Type.is_con()
  public boolean should_con(Type t) {
    if( this instanceof ConNode || // Already a constant
        (this instanceof FunPtrNode && _val.is_con()) || // Already a constant
        this instanceof ErrNode || // Never touch an ErrNode
        this instanceof FreshNode ||// These modify the TVars but not the constant flows
        is_prim() )                // Never touch a Primitive
      return false; // Already a constant, or never touch an ErrNode
    // Constant argument to call: keep for call resolution.
    // Call can always inline to fold constant.
    if( this instanceof ProjNode && in(0) instanceof CallNode && ((ProjNode)this)._idx>0 )
      return false;
    // Is a constant and not in error?  Do not remove the error.
    return t.is_con() && err(true) == null;
  }

  // Make globally shared common ConNode for this type.
  public static @NotNull Node con( Type t ) {
    assert t==t.simple_ptr();
    if( t instanceof TypeFunPtr && ((TypeFunPtr)t)._fidxs.abit()!=-1 )
      return ValFunNode.get(((TypeFunPtr)t)._fidxs.getbit()); // Pre-existing function constant
    Node con = new ConNode<>(t);
    Node con2 = VALS.get(con);
    if( con2 != null ) {        // Found a prior constant
      con.kill();               // Kill the just-made one
      con = con2;
      con._live = TypeMem.ALIVE;// Adding more liveness
    } else {                    // New constant
      con._val = t;             // Typed
      con._elock(); // Put in VALS, since if Con appears once, probably appears again in the same XFORM call
    }
    return Env.GVN.add_flow(con); // Updated live flows
  }

  // Forward reachable walk, setting types to ANY and making all dead.
  public final void walk_initype(  ) {
    if( Env.GVN.on_flow(this) ) return; // Been there, done that
    Env.GVN.add_flow(this);             // On worklist and mark visited
    if( AA.DO_GCP ) {
      _val = Type.ANY;          // Highest value
      _live = TypeMem.DEAD;     // Not alive
      if( this instanceof CallNode ) (( CallNode)this)._not_resolved_by_gcp = false; // Try again
    } else {                    // Not doing optimistic GCP...
      assert _val==value() && _live==live();
    }
    if( AA.DO_HMT ) {
      _tvar = new_tvar("Combo");
      //if( this instanceof FreshNode) ((FreshNode)this).id().tvar().push_dep(this);
      //if( this instanceof ProjNode && ((ProjNode)this)._idx==DSP_IDX && in(0) instanceof CallNode )
      //  ((CallNode)in(0)).fdx().tvar().push_dep(this);
    }
    // Walk reachable graph
    for( Node use : _uses )                   use.walk_initype();
    for( Node def : _defs ) if( def != null ) def.walk_initype();
  }

  public final void walk_record_for_reset( ) {
    if( Env.GVN.on_flow(this) ) return; // Been there, done that
    Env.GVN.add_flow(this);
    for( Node use : _uses )                   use.walk_record_for_reset();
    for( Node def : _defs ) if( def != null ) def.walk_record_for_reset();
    record_for_reset();
  }
  void record_for_reset() { }

  // Reset
  public final void walk_reset( ) {
    if( Env.GVN.on_flow(this) ) return; // Been there, done that
    Env.GVN.add_flow(this);             // On worklist and mark visited
    _val = Type.ALL;                    // Lowest value
    _live = all_live();                 // Full alive
    _elock = false;                     // Clear elock if reset_to_init0
    _tvar = null;
    // Walk reachable graph
    for( Node use : _uses )                   use.walk_reset();
    for( Node def : _defs ) if( def != null ) def.walk_reset();
    if( this instanceof NewNode ) ((NewNode)this).reset();
    if( this instanceof CallNode ) ((CallNode)this)._not_resolved_by_gcp = false; // Try again
    if( this instanceof RegionNode || this instanceof PhiNode ) {
      while( len()>1 && !in(len()-1).is_prim() )
        pop(); // Kill wired primitive inputs
    }
  }


  // At least as alive
  private Node merge(Node x) {
    x._live = (TypeMem)x._live.meet(_live);
    return Env.GVN.add_flow(x);
  }

  // Node n is new in Combo (NOT GCP), cannot do most graph-reshape but
  // commonly hit in VALS and this is OK.
  public Node init1( ) {
    Node x = VALS.get(this);
    if( x!=null ) {             // Hit in GVN table
      //kill();                   // Kill just-init'd
      //return x;                 // Return old, which will add uses
      throw unimpl("untested");
    }
    _elock();                   // Install in GVN
    _val = Type.ANY;            // Super optimistic types
    _live = TypeMem.DEAD;
    return Env.GVN.add_flow(this);
  }

  // Assert all ideal, value and liveness calls are done
  public final boolean more_ideal(VBitSet bs) {
    if( bs.tset(_uid) ) return false; // Been there, done that
    if( !is_keep() ) { // Only non-keeps, which is just top-level scope and prims
      Node x;
      x = do_reduce(); if( x != null )
                         return true; // Found an ideal call
      x = do_mono  (); if( x != null )
                         return true; // Found an ideal call
      x = do_grow  (); if( x != null )
                         return true; // Found an ideal call
      if( this instanceof FunNode ) ((FunNode)this).ideal_inline(true);
    }
    for( Node def : _defs ) if( def != null && def.more_ideal(bs) ) return true;
    for( Node use : _uses ) if( use != null && use.more_ideal(bs) ) return true;
    return false;
  }

  // Assert all value and liveness calls only go forwards.  Returns >0 for failures.
  private static final VBitSet FLOW_VISIT = new VBitSet();
  public  final int more_work( boolean lifting ) { FLOW_VISIT.clear();  return more_work(lifting,0);  }
  private int more_work( boolean lifting, int errs ) {
    if( FLOW_VISIT.tset(_uid) ) return errs; // Been there, done that
    if( Env.GVN.on_dead(this) ) return errs; // Do not check dying nodes
    // Check for GCP progress
    Type    oval= _val, nval = value(); // Forwards flow
    TypeMem oliv=_live, nliv = live (); // Backwards flow
    if( oval!=nval || oliv!=nliv ) {
      if( !(lifting
            ? nval.isa(oval) && nliv.isa(oliv)
            : oval.isa(nval) && oliv.isa(nliv)) )
        errs += _report_bug("Monotonicity bug");
      if( !Env.GVN.on_flow(this) &&
          (lifting || AA.DO_GCP) )
        errs += _report_bug("Progress bug");
    }
    // Check for HMT progress
    if( AA.DO_HMT && oliv!=TypeMem.DEAD && _tvar!=null ) {
      if( unify(true) ) {
        if( Combo.HM_FREEZE ) errs += _report_bug("Progress after freezing");
        if( !Env.GVN.on_flow(this) ) errs += _report_bug("Progress bug");
      }
    }
    for( Node def : _defs ) if( def != null ) errs = def.more_work(lifting,errs);
    for( Node use : _uses ) if( use != null ) errs = use.more_work(lifting,errs);
    return errs;
  }
  private int _report_bug(String msg) {
    FLOW_VISIT.clear(_uid); // Pop-frame & re-run in debugger
    System.err.println(msg);
    System.err.println(dump(0,new SB(),true)); // Rolling backwards not allowed
    return 1;
  }


  // Gather errors, walking from Scope to START.
  public void walkerr_def( HashSet<ErrMsg> errs, VBitSet bs ) {
    if( bs.tset(_uid) ) return; // Been there, done that
    for( int i=0; i<_defs._len; i++ ) {
      Node def = _defs.at(i);   // Walk data defs for more errors
      if( def == null || def._val == Type.XCTRL ) continue;
      // Walk function bodies that are wired
      if( def instanceof FunPtrNode && !(this instanceof ScopeNode) )
        continue;
      def.walkerr_def(errs,bs);
    }
    if( is_prim() ) return;
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

  // GCP optimizations on the live subgraph
  public void walk_opt( VBitSet visit ) {
    assert !is_dead();
    if( visit.tset(_uid) ) return; // Been there, done that
    _elock = false;                // Removed from VALS
    // Walk reachable graph
    if( is_dead() ) return;
    Env.GVN.add_work_new(this);
    for( Node def : _defs )  if( def != null )  def.walk_opt(visit);
    for( Node use : _uses )                     use.walk_opt(visit);
  }

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
  // For most memory-producing Nodes, exactly 1 memory producer follows.
  public Node get_mem_writer() {
    for( Node use : _uses ) if( use.is_mem() ) return use;
    return null;
  }
  // Easy assertion check
  boolean check_solo_mem_writer(Node memw) {
    boolean found=false;
    for( Node use : _uses )
      if( use == memw ) found=true; // Only memw mem-writer follows
      else if( use.is_mem() ) return false; // Found a 2nd mem-writer
    return found;
  }

  // Shortcut
  public Type sharptr( Node mem ) { return mem._val.sharptr(_val); }

  // Aliases that a MemJoin might choose between.  Not valid for nodes which do
  // not manipulate memory.
  BitsAlias escapees() { throw unimpl("graph error"); }

  // Return a node for a java Class.  Used by the primitives.
  public Node clazz_node() { throw unimpl(); }

  // Walk a subset of the dominator tree, looking for the last place (highest
  // in tree) this predicate passes, or null if it never does.
  Node walk_dom_last(Predicate<Node> P) {
    assert in(0) != null;       // All default control nodes pass ctrl in slot 0
    Node n = in(0).walk_dom_last(P);
    if( n != null ) return n;   // Take last answer first
    return P.test(this) ? this : null;
  }
}
