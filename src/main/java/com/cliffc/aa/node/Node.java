package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.HashSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;

/**
 * Sea-of-Nodes
 */
public abstract class Node implements Cloneable {
  static final byte OP_CALL   = 1;
  static final byte OP_CALLEPI= 2;
  static final byte OP_CAST   = 3;
  static final byte OP_CON    = 4;
  static final byte OP_CONTYPE= 5;
  static final byte OP_CPROJ  = 6;
  static final byte OP_DEFMEM = 7;
  static final byte OP_ERR    = 8;
  static final byte OP_FRESH  = 9;
  static final byte OP_FP2DISP=10;
  static final byte OP_FUN    =11;
  static final byte OP_FUNPTR =12;
  static final byte OP_IF     =13;
  static final byte OP_JOIN   =14;
  static final byte OP_LOAD   =15;
  static final byte OP_LOOP   =16;
  static final byte OP_NAME   =17; // Cast a prior NewObj to have a runtime Name
  static final byte OP_NEWOBJ =18; // Allocate a new struct
  static final byte OP_NEWARY =19; // Allocate a new array
  static final byte OP_NEWSTR =20; // Allocate a new string
  static final byte OP_PARM   =21;
  static final byte OP_PHI    =22;
  static final byte OP_PRIM   =23;
  static final byte OP_PROJ   =24;
  static final byte OP_REGION =25;
  static final byte OP_RET    =26;
  static final byte OP_SCOPE  =27;
  static final byte OP_SPLIT  =28;
  static final byte OP_START  =29;
  static final byte OP_STMEM  =30;
  static final byte OP_STORE  =31;
  static final byte OP_THRET  =32;
  static final byte OP_THUNK  =33;
  static final byte OP_TYPE   =34;
  static final byte OP_UNR    =35;
  static final byte OP_MAX    =36;

  private static final String[] STRS = new String[] { null, "Call", "CallEpi", "Cast", "Con", "ConType", "CProj", "DefMem", "Err", "Fresh", "FP2Disp", "Fun", "FunPtr", "If", "Join", "Load", "Loop", "Name", "NewObj", "NewAry", "NewStr", "Parm", "Phi", "Prim", "Proj", "Region", "Return", "Scope","Split", "Start", "StartMem", "Store", "Thret", "Thunk", "Type", "Unresolved" };
  static { assert STRS.length==OP_MAX; }

  // Unique dense node-numbering
  public  static int _INIT0_CNT;
  private static int CNT=1; // Do not hand out UID 0
  private static final VBitSet LIVE = new VBitSet();  // Conservative approximation of live; due to loops some things may be marked live, but are dead
  int newuid() {
    assert CNT < 100000 : "infinite node create loop";
    if( CNT==AA.UID )
      System.out.print("");
    LIVE.set(CNT);
    return CNT++;
  }

  // Initial state after loading e.g. primitives.
  public static void init0() {
    assert LIVE.get(CNT-1) && !LIVE.get(CNT);
    _INIT0_CNT=CNT;
  }
  /**
   * Reset is called after a top-level exec exits (e.g. junits) with no parse
   * state left alive.  NOT called after a line in the REPL or a user-call to
   * "eval" as user state carries on.
   */
  public static void reset_to_init0() {
    CNT = 0;
    LIVE.clear();
    VALS.clear();
  }


  public int _uid;      // Unique ID, will have gaps, used to give a dense numbering to nodes
  final byte _op;       // Opcode (besides the object class), used to avoid v-calls in some places
  public byte _keep;    // Keep-alive in parser, even as last use goes away
  public boolean _elock;// Edge-lock: cannot modify edges because messes up hashCode & GVN
  public Type _val;     // Value; starts at ALL and lifts towards ANY.
  public TypeMem _live; // Liveness; assumed live in gvn.iter(), assumed dead in gvn.gcp().
  // Hindley-Milner inspired typing, or CNC Thesis based congruence-class
  // typing.  This is a Type Variable which can unify with other TV2s forcing
  // Type-equivalence (JOIN of unified Types), and includes gross structure
  // (functions, structs, pointers, or simple Types).
  @NotNull TV2 _tvar;
  // H-M Type-Variables
  public TV2 tvar() {
    TV2 tv = _tvar.find();     // Do U-F step
    return tv == _tvar ? tv : (_tvar = tv); // Update U-F style in-place.
  }
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

  private boolean check_vals( ) {
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
    if( old._uses._len!=0 && old._keep ==0 ) old.add_flow_def_extra(this);
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
  public Node subsume( Node nnn ) {
    assert !nnn.is_dead();
    insert(nnn);                // Change graph shape
    nnn.keep();                 // Keep-alive
    kill();                     // Delete the old, and anything it uses
    return nnn.unkeep();        // Remove keep-alive
  }

  // Kill a node; all inputs are null'd out; this may put more dead Nodes on
  // the dead worklist.  Return this for progress, null for no-progress.
  public Node kill( ) {
    if( is_dead() ) return null;
    assert _uses._len==0 && _keep==0;
    // Similar to unelock(), except do not put on any worklist
    if( _elock ) { _elock = false; Node x = VALS.remove(this); assert x == this; }
    while( _defs._len > 0 ) unuse(_defs.pop());
    set_dead();                 // officially dead now
    LIVE.clear(_uid);           // Off the LIVE set.  CNT cannot roll back unless the GVN worklists are also clear
    return this;
  }
  // Called when GVN worklists are empty
  public static void roll_back_CNT() { while( !LIVE.get(CNT-1) ) CNT--; }

  // "keep" a Node during all optimizations because it is somehow unfinished.
  // Typically used when needing to build several Nodes before building the
  // typically using Node; during construction the earlier Nodes have no users
  // (yet) and are not dead.  Acts "as if" there is an unknown user.
  public <N extends Node> N keep() { return keep(1); }
  @SuppressWarnings("unchecked")
  public <N extends Node> N keep(int d) { _keep+=d;  return (N)this; }
  // Remove the keep flag, but do not delete.
  public <N extends Node> N unkeep() { return unkeep(1); }
  @SuppressWarnings("unchecked")
  public <N extends Node> N unkeep(int d) {
    assert _keep >= d; _keep-=d;
    return (N)this;
  }
  // Remove the keep flag, and immediately allow optimizations.
  public <N extends Node> N unhook() {
    if( _keep==1 ) Env.GVN.add_work_all(this);
    return unkeep();
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
    _tvar = new_tvar("constructor");
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
      n._tvar = n.new_tvar("copy_constructor");
      n._keep = 0;              // Not keeping, even if cloning a mid-keeper operation
      n._elock=false;           // Not in GVN
      if( copy_edges )
        for( Node def : _defs )
          n.add_def(def);
      Env.GVN.add_work_all(n);
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
      if( !(n._uid <= Env.ALL_CTRL._uid || !n.is_prim() || prims) )
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
  abstract public Type value(GVNGCM.Mode opt_mode);

  // Shortcut to update self-value.  Typically used in contexts where it is NOT
  // locally monotonic - hence we cannot run any monotonicity asserts until the
  // invariant is restored over the entire region.
  public Type xval( ) {
    Type oval = _val;                     // Get old type
    Type nval = value(Env.GVN._opt_mode); // Get best type
    if( nval!=oval ) {
      _val = nval;
      Env.GVN.add_flow_uses(this); // Put uses on worklist... values flows downhill
    }
    return nval;
  }

  public Type val(int idx) { return in(idx)._val; }

  // Compute the current best liveness for this Node, based on the liveness of
  // its uses.  If basic_liveness(), returns a simple DEAD/ALIVE.  Otherwise
  // computes the alive memory set down to the field level.  May return
  // TypeMem.FULL, especially if its uses are of unwired functions.
  // It must be monotonic.
  // This is a reverse-flow transfer-function computation.
  public TypeMem live( GVNGCM.Mode opt_mode ) {
    if( _keep>0 ) return all_live();
    // Compute meet/union of all use livenesses
    TypeMem live = TypeMem.DEAD; // Start at lattice top
    for( Node use : _uses )      // Computed across all uses
      if( use.live_uses() ) {
        TypeMem ulive = use.live_use(opt_mode, this);
        live = (TypeMem)live.meet(ulive); // Make alive used fields
      }
    assert live==TypeMem.DEAD || live.basic_live()==all_live().basic_live();
    assert live!=TypeMem.LIVE_BOT || (_val !=Type.CTRL && _val !=Type.XCTRL);
    return live;
  }
  public boolean live_uses() {
    return _live != TypeMem.DEAD &&    // Only live uses make more live
      // And no chance use turns into a constant (which then does not use anything)
      !(_live.basic_live() && _val.may_be_con() && !is_prim() && err(true)==null &&
        // FunPtrs still use their Rets, even if constant
        !(this instanceof FunPtrNode));
  }

  // Shortcut to update self-live
  public Node xliv( GVNGCM.Mode opt_mode ) { _live = live(opt_mode); return this; }
  // Compute local contribution of use liveness to this def.
  // Overridden in subclasses that do per-def liveness.
  public TypeMem live_use( GVNGCM.Mode opt_mode, Node def ) {
    return _keep>0 ? all_live() : _live;
  }

  // Default lower-bound liveness.  For control, its always "ALIVE" and for
  // memory opts (and tuples with memory) its "ALLMEM".
  public TypeMem all_live() { return TypeMem.LIVE_BOT; }

  // The _val changed here, and more than the immediate _neighbors might change
  // value/live
  public void add_flow_extra(Type old) { }
  public void add_flow_use_extra(Node chg) { }
  public void add_flow_def_extra(Node chg) { }
  // Inputs changed here, and more than the immediate _neighbors might reduce
  public void add_reduce_extra() { }

  // Unifies this Node with others; Call/CallEpi with Fun/Parm/Ret.  NewNodes &
  // Load/Stores, etc.  Returns true if progress, and puts neighbors back on
  // the worklist.  If 'test' then make no changes, but return if progress
  // would be made.
  public boolean unify(boolean test) { return false; }

  // Return any type error message, or null if no error
  public ErrMsg err( boolean fast ) { return null; }

  // Operator precedence is only valid for binary functions.
  // 1-9: Normal precedence
  // 0  : Balanced op; precedence is from Parse.term() and not expr().
  // -1 : Invalid
  // -2 : Forward ref.
  public byte op_prec() { return -1; }


  // Global expressions, to remove redundant Nodes
  public static final ConcurrentHashMap<Node,Node> VALS = new ConcurrentHashMap<>();

  // Reducing xforms, strictly fewer Nodes or Edges.  n may be either in or out
  // of VALS.  If a replacement is found, replace.  In any case, put in the
  // VALS table.  Return null if no progress, or this or the replacement.
  // If keep is 0, there are no hidden users and can hack away.
  // If keep is 1, there is exactly one hidden user, which will use the returned replacement.
  // If keep is 2+, there are many hidden users and the Node cannot be replaced.
  public Node do_reduce() {
    assert check_vals();
    Node nnn = _do_reduce();
    if( nnn!=null ) {                   // Something happened
      if( nnn!=this ) {                 // Replacement
        assert _keep<=1;                // Can only replace if zero or one
        Env.GVN.add_flow_uses(this);    // Visit users
        add_reduce_extra();
        if( _keep==1 ) { _keep--; nnn._keep++; } // Move keep bits over
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
    if( !_elock ) {             // Not in VALS
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
    // Compute live bits.  If progress, push the defs on the flow worklist.
    // This is a reverse flow computation.  Always assumed live if keep.
    if( _keep==0 ) {
      TypeMem oliv = _live;
      TypeMem nliv = live(Env.GVN._opt_mode);
      if( oliv != nliv ) {        // Progress?
        progress = this;          // Progress!
        assert nliv.isa(oliv);    // Monotonically improving
        _live = nliv;             // Record progress
        for( Node def : _defs )   // Put defs on worklist... liveness flows uphill
          if( def != null ) Env.GVN.add_flow(def).add_flow_def_extra(this);
        add_flow_extra(oliv);
      }
    }

    // Compute best value.  If progress, push uses on the flow worklist.
    // This is a forward flow computation.
    Type oval = _val; // Get old type
    Type nval = value(Env.GVN._opt_mode);// Get best type
    if( nval!=oval ) {
      progress = this;          // Progress!
      assert nval.isa(oval);    // Monotonically improving
      _val = nval;
      // If becoming a constant, check for replacing with a ConNode
      if( !oval.may_be_con() && nval.may_be_con() ) {
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
    assert _keep<=1;
    if( _keep==1 ) { _keep--; nnn._keep++; Env.GVN.add_dead(this); } // Doing an arbitrary replacement
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
    // Is in-error; do not remove the error.
    if( err(true) != null )
      return false;
    // Is a constant
    return t.is_con();
  }

  // Make globally shared common ConNode for this type.
  public static @NotNull Node con( Type t ) {
    assert t==t.simple_ptr();
    Node con;
    if( t instanceof TypeFunPtr && ((TypeFunPtr)t)._fidxs.abit()!=-1 )
      con = new FunPtrNode(FunNode.find_fidx(((TypeFunPtr)t).fidx()).ret(),Env.ANY);
    else
      con = new ConNode<>(t);
    Node con2 = VALS.get(con);
    if( con2 != null ) {        // Found a prior constant
      con.kill();               // Kill the just-made one
      con = con2;
      con._live = TypeMem.LIVE_BOT; // Adding more liveness
    } else {                        // New constant
      con._val = t;                 // Typed
      con._elock(); // Put in VALS, since if Con appears once, probably appears again in the same XFORM call
    }
    Env.GVN.add_flow(con);      // Updated live flows
    return con;
  }

  // Forward reachable walk, setting types to ANY and making all dead.
  public final void walk_initype( GVNGCM gvn, VBitSet bs ) {
    if( bs.tset(_uid) ) return;    // Been there, done that
    _val = Type.ANY;               // Highest value
    _live = TypeMem.DEAD;          // Not alive
    // Walk reachable graph
    gvn.add_flow(this);
    for( Node use : _uses ) use.walk_initype(gvn,bs);
    for( Node def : _defs ) if( def != null ) def.walk_initype(gvn,bs);
  }

  // At least as alive
  private Node merge(Node x) {
    x._live = (TypeMem)x._live.meet(_live);
    return Env.GVN.add_flow(x);
  }

  // Node n is new, but cannot call GVN.iter() so cannot call the general xform.
  public Node init1( ) {
    Node x = VALS.get(this);
    if( Env.GVN._opt_mode == GVNGCM.Mode.Opto ) _live = TypeMem.DEAD;
    if( x!=null ) {             // Hit in GVN table
      merge(x);
      kill();                                 // Kill just-init'd
      return x;                               // Return old
    }
    _elock();
    _val = value(Env.GVN._opt_mode);
    return Env.GVN.add_work_all(this);
  }

  // Assert all ideal, value and liveness calls are done
  public final boolean more_ideal(VBitSet bs) {
    if( bs.tset(_uid) ) return false; // Been there, done that
    if( _keep == 0 && _live.is_live() ) { // Only non-keeps, which is just top-level scope and prims
      Type t = value(Env.GVN._opt_mode);
      if( _val != t )
        return true;            // Found a value improvement
      TypeMem live = live(Env.GVN._opt_mode);
      if( _live != live )
        return true;            // Found a liveness improvement
      Node x;
      x = do_reduce(); if( x != null )
                         return true; // Found an ideal call
      x = do_mono(); if( x != null )
                       return true; // Found an ideal call
      x = do_grow(); if( x != null )
                       return true; // Found an ideal call
      if( this instanceof FunNode ) ((FunNode)this).ideal_inline(true);
    }
    for( Node def : _defs ) if( def != null && def.more_ideal(bs) ) return true;
    for( Node use : _uses ) if( use != null && use.more_ideal(bs) ) return true;
    return false;
  }

  // Assert all value and liveness calls only go forwards.  Returns >0 for failures.
  private static final VBitSet FLOW_VISIT = new VBitSet();
  public  final int more_flow(boolean lifting) { FLOW_VISIT.clear();  return more_flow(lifting,0);  }
  private int more_flow( boolean lifting, int errs ) {
    if( FLOW_VISIT.tset(_uid) ) return errs; // Been there, done that
    if( Env.GVN.on_dead(this) ) return errs; // Do not check dying nodes
    // Check for only forwards flow, and if possible then also on worklist
    Type    oval= _val, nval = value(Env.GVN._opt_mode);
    TypeMem oliv=_live, nliv = live (Env.GVN._opt_mode);
    boolean hm = false;
    if( nval != oval || nliv != oliv || hm ) {
      boolean ok = lifting
        ? nval.isa(oval) && nliv.isa(oliv)
        : oval.isa(nval) && oliv.isa(nliv);
      if( !ok || (!Env.GVN.on_flow(this) && !Env.GVN.on_dead(this) && _keep==0) ) { // Still-to-be-computed?
        FLOW_VISIT.clear(_uid); // Pop-frame & re-run in debugger
        System.err.println(dump(0,new SB(),true)); // Rolling backwards not allowed
        errs++;
      }
    }
    for( Node def : _defs ) if( def != null ) errs = def.more_flow(lifting,errs);
    for( Node use : _uses ) if( use != null ) errs = use.more_flow(lifting,errs);
    return errs;
  }

  // Gather errors, walking from Scope to START.
  public void walkerr_def( HashSet<ErrMsg> errs, VBitSet bs ) {
    if( bs.tset(_uid) ) return; // Been there, done that
    for( int i=0; i<_defs._len; i++ ) {
      Node def = _defs.at(i);   // Walk data defs for more errors
      if( def == null || def._val == Type.XCTRL ) continue;
      // Walk function bodies that are wired, but not bare FunPtrs.
      if( def instanceof FunPtrNode && !def.is_forward_ref() )
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

    // Replace any constants.  Since the node computes a constant, its inputs
    // were never marked live, and so go dead and so go to ANY and so are not
    // available to recompute the constant later.
    Type val = _val;
    TypeFunPtr tfp;
    if( val instanceof TypeFunPtr &&
        _live.live_no_disp() &&
        (tfp=(TypeFunPtr)val)._disp!=TypeMemPtr.NO_DISP )
      val = tfp.make_no_disp();
    if( should_con(val) )
      subsume(con(val)).xliv(GVNGCM.Mode.Opto);

    // Walk reachable graph
    if( is_dead() ) return;
    Env.GVN.add_work_all(this);
    for( Node def : _defs )  if( def != null )  def.walk_opt(visit);
    for( Node use : _uses )                     use.walk_opt(visit);
  }

  public boolean is_dead() { return _uses == null; }
  public void set_dead( ) { _defs = _uses = null; }   // TODO: Poor-mans indication of a dead node, probably needs to recycle these...

  // Overridden in subclasses that return TypeTuple value types.  Such nodes
  // are always followed by ProjNodes to break out the tuple slices.  If the
  // node optimizes, each ProjNode becomes a copy of some other value... based
  // on the ProjNode index
  public Node is_copy(int idx) { return null; }

  // Only true for some RetNodes and FunNodes
  public boolean is_forward_ref() { return false; }

  // True if this Call/CallEpi pair does not read or write memory.
  // True for most primitives.  Returns the pre-call memory or null.
  Node is_pure_call() { return null; }

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
    if( is_prim() ) return true; // Several top-level memory primitives, including top scope & defmem blow this
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

  // Walk a subset of the dominator tree, looking for the last place (highest
  // in tree) this predicate passes, or null if it never does.
  Node walk_dom_last(Predicate<Node> P) {
    assert in(0) != null;       // All default control nodes pass ctrl in slot 0
    Node n = in(0).walk_dom_last(P);
    if( n != null ) return n;   // Take last answer first
    return P.test(this) ? this : null;
  }

  // ----------------------------------------------
  // Error levels
  public enum Level {
    ForwardRef,               // Forward refs
    ErrNode,                  // ErrNodes
    Syntax,                   // Syntax
    Field,                    // Field naming errors
    TypeErr,                  // Type errors
    NilAdr,                   // Address might be nil on mem op
    BadArgs,                  // Unspecified primitive bad args
    UnresolvedCall,           // Unresolved calls
    AllTypeErr,               // Type errors, with one of the types All
    Assert,                   // Assert type errors
    TrailingJunk,             // Trailing syntax junk
    MixedPrimGC,              // Mixed primitives & GC
  }

  // Error messages
  public static class ErrMsg implements Comparable<ErrMsg> {
    public       Parse _loc;    // Point in code to blame
    public final String _msg;   // Printable error message, minus code context
    public final Level _lvl;    // Priority for printing
    public int _order;          // Message order as they are found.
    public static final ErrMsg FAST = new ErrMsg(null,"fast",Level.Syntax);
    public static final ErrMsg BADARGS = new ErrMsg(null,"bad arguments",Level.BadArgs);
    public ErrMsg(Parse loc, String msg, Level lvl) { _loc=loc; _msg=msg; _lvl=lvl; }
    public static ErrMsg forward_ref(Parse loc, FunPtrNode fun) { return forward_ref(loc,fun._name); }
    public static ErrMsg forward_ref(Parse loc, String name) {
      return new ErrMsg(loc,"Unknown ref '"+name+"'",Level.ForwardRef);
    }
    public static ErrMsg syntax(Parse loc, String msg) {
      return new ErrMsg(loc,msg,Level.Syntax);
    }
    public static ErrMsg unresolved(Parse loc, String msg) {
      return new ErrMsg(loc,msg,Level.UnresolvedCall);
    }
    public static ErrMsg typerr( Parse loc, Type actual, Type t0mem, Type expected ) { return typerr(loc,actual,t0mem,expected,Level.TypeErr); }
    public static ErrMsg typerr( Parse loc, Type actual, Type t0mem, Type expected, Level lvl ) {
      TypeMem tmem = t0mem instanceof TypeMem ? (TypeMem)t0mem : null;
      VBitSet vb = new VBitSet();
      SB sb = actual.str(new SB(),vb, tmem, false).p(" is not a ");
      vb.clear();
      expected.str(sb,vb,null,false); // Expected is already a complex ptr, does not depend on memory
      if( actual==Type.ALL && lvl==Level.TypeErr ) lvl=Level.AllTypeErr; // ALLs have failed earlier, so this is a lower priority error report
      return new ErrMsg(loc,sb.toString(),lvl);
    }
    public static ErrMsg typerr( Parse loc, Type actual, Type t0mem, Type[] expecteds ) {
      TypeMem tmem = t0mem instanceof TypeMem ? (TypeMem)t0mem : null;
      VBitSet vb = new VBitSet();
      SB sb = actual.str(new SB(),vb, tmem,false);
      sb.p( expecteds.length==1 ? " is not a " : " is none of (");
      vb.clear();
      for( Type expect : expecteds ) expect.str(sb,vb,null,false).p(',');
      sb.unchar().p(expecteds.length==1 ? "" : ")");
      return new ErrMsg(loc,sb.toString(),Level.TypeErr);
    }
    public static ErrMsg asserterr( Parse loc, Type actual, Type t0mem, Type expected ) {
      return typerr(loc,actual,t0mem,expected,Level.Assert);
    }
    public static ErrMsg field(Parse loc, String msg, String fld, boolean closure, TypeObj to) {
      SB sb = new SB().p(msg).p(closure ? " val '" : " field '.").p(fld).p("'");
      if( to != null && !closure ) to.str(sb.p(" in "),new VBitSet(),null,false);
      return new ErrMsg(loc,sb.toString(),Level.Field);
    }
    public static ErrMsg niladr(Parse loc, String msg, String fld) {
      String f = fld==null ? msg : msg+" field '."+fld+"'";
      return new ErrMsg(loc,f,Level.NilAdr);
    }
    public static ErrMsg badGC(Parse loc) {
      return new ErrMsg(loc,"Cannot mix GC and non-GC types",Level.MixedPrimGC);
    }
    public static ErrMsg trailingjunk(Parse loc) {
      return new ErrMsg(loc,"Syntax error; trailing junk",Level.TrailingJunk);
    }

    @Override public String toString() {
      return _loc==null ? _msg : _loc.errLocMsg(_msg);
    }
    @Override public int compareTo(ErrMsg msg) {
      int cmp = _lvl.compareTo(msg._lvl);
      if( cmp != 0 ) return cmp;
      return _order - msg._order;
      //cmp = _loc.compareTo(msg._loc);
      //if( cmp != 0 ) return cmp;
      //return _msg.compareTo(msg._msg);
    }
    @Override public boolean equals(Object obj) {
      if( this==obj ) return true;
      if( !(obj instanceof ErrMsg) ) return false;
      ErrMsg err = (ErrMsg)obj;
      if( _lvl!=err._lvl || !_msg.equals(err._msg) ) return false;
      // Spread a missing loc; cheaty but only a little bit.
      // TODO: track down missing loc in Parser
      if( _loc==null && err._loc!=null ) _loc=err._loc;
      if( _loc!=null && err._loc==null ) err._loc=_loc;
      return _loc==err._loc || _loc.equals(err._loc);
    }
    @Override public int hashCode() {
      return (_loc==null ? 0 : _loc.hashCode())+_msg.hashCode()+_lvl.hashCode();
    }
  }

}
