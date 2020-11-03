package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.TNode;
import com.cliffc.aa.tvar.TVar;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.HashSet;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.MEM_IDX;

// Sea-of-Nodes
public abstract class Node implements Cloneable, TNode {
  static final byte OP_CALL   = 1;
  static final byte OP_CALLEPI= 2;
  static final byte OP_CAST   = 3;
  static final byte OP_CON    = 4;
  static final byte OP_CPROJ  = 5;
  static final byte OP_DEFMEM = 6;
  static final byte OP_ERR    = 7;
  static final byte OP_FP2CLO = 8;
  static final byte OP_FUN    = 9;
  static final byte OP_FUNPTR =10;
  static final byte OP_IF     =11;
  static final byte OP_JOIN   =12;
  static final byte OP_LOAD   =13;
  static final byte OP_LOOP   =14;
  static final byte OP_NAME   =15; // Cast a prior NewObj to have a runtime Name
  static final byte OP_NEWOBJ =16; // Allocate a new struct
  static final byte OP_NEWARY =17; // Allocate a new array
  static final byte OP_NEWSTR =18; // Allocate a new string
  static final byte OP_PARM   =19;
  static final byte OP_PHI    =20;
  static final byte OP_PRIM   =21;
  static final byte OP_PROJ   =22;
  static final byte OP_REGION =23;
  static final byte OP_RET    =24;
  static final byte OP_SCOPE  =25;
  static final byte OP_SPLIT  =26;
  static final byte OP_START  =27;
  static final byte OP_STMEM  =28;
  static final byte OP_STORE  =29;
  static final byte OP_THRET  =30;
  static final byte OP_THUNK  =31;
  static final byte OP_TYPE   =32;
  static final byte OP_UNR    =33;
  static final byte OP_MAX    =34;

  private static final String[] STRS = new String[] { null, "Call", "CallEpi", "Cast", "Con", "CProj", "DefMem", "Err", "FP2Clo", "Fun", "FunPtr", "If", "Join", "Load", "Loop", "Name", "NewObj", "NewAry", "NewStr", "Parm", "Phi", "Prim", "Proj", "Region", "Return", "Scope","Split", "Start", "StartMem", "Store", "Thret", "Thunk", "Type", "Unresolved" };
  static { assert STRS.length==OP_MAX; }

  public int _uid;      // Unique ID, will have gaps, used to give a dense numbering to nodes
  final byte _op;       // Opcode (besides the object class), used to avoid v-calls in some places
  public byte _keep;    // Keep-alive in parser, even as last use goes away
  public boolean _in;   // "in" or "out" of GVN...
  public TypeMem _live; // Liveness; assumed live in gvn.iter(), assumed dead in gvn.gcp().
  @NotNull TVar _tvar;  // Type variable; has a Type which starts at ALL and lifts towards ANY, and may have constraints to be equal to other Types
  public Type val() { return _tvar.type(); } // The unified Type
  public Type oval() { return _tvar._type(false); } // The local, not-unified, Type
  public Type set_val( @NotNull Type val ) {
    _in = true;
    assert _tvar.uid()==_uid;
    return _tvar.setype(val);
  }
  public TVar tvar() { return _tvar; }
  public TVar tvar(int x) { return in(x)._tvar; }
  public @NotNull TNode[] parms () { throw com.cliffc.aa.AA.unimpl(); } // Only for  FunNodes
  public @NotNull String @NotNull [] argnames() { throw com.cliffc.aa.AA.unimpl(); } // Only for FunNodes

  // Defs.  Generally fixed length, ordered, nulls allowed, no unused trailing space.  Zero is Control.
  public Ary<Node> _defs;
  public void _chk() { assert Env.GVN.check_out(this); }
  // Add def/use edge
  public Node add_def(Node n) { _chk(); _defs.add(n); if( n!=null ) n._uses.add(this); return this; }
  // Replace def/use edge
  public Node set_def( int idx, Node n, GVNGCM gvn ) {
    _chk();
    Node old = _defs.at(idx);  // Get old value
    // Add edge to new guy before deleting old, in case old goes dead and
    // recursively makes new guy go dead also
    if( (_defs._es[idx] = n) != null ) n._uses.add(this);
    return unuse(old, gvn);
  }
  public Node swap_def( int idx, Node n, GVNGCM gvn ) {
    _chk();
    Node old = _defs.at(idx);  // Get old value
    // Add edge to new guy before deleting old, in case old goes dead and
    // recursively makes new guy go dead also
    if( (_defs._es[idx] = n) != null ) n._uses.add(this);
    if( old != null ) old._uses.del(this);
    return old;
  }

  public Node insert (int idx, Node n) { _chk(); _defs.insert(idx,n); if( n!=null ) n._uses.add(this); return this; }
  // Return Node at idx, withOUT auto-deleting it, even if this is the last
  // use.  Used by the parser to retrieve final Nodes from tmp holders.  Does
  // NOT preserve order.
  public Node del( int idx ) {
    _chk();
    Node n = _defs.del(idx);
    if( n != null ) n._uses.del(this);
    return n;
  }
  public Node in( int i) { return _defs.at(i); }
  private Node unuse( Node old, GVNGCM gvn ) {
    if( old != null ) {
      old._uses.del(this);
      if( old._uses._len==0 && old._keep==0 ) { // Recursively begin deleting
        Node x0 = old.in(0);
        gvn.kill(old);          // Recursively delete
        if( x0 != null && !x0.is_dead() && old instanceof ProjNode ) { // Remove a projection can make a is_copy input go dead
          Node x1 = x0._defs.atX(((ProjNode)old)._idx);
          if( x1 != null ) gvn.add_work(x1);
        }
      }
      if( !old.is_dead() ) {
        // TODO: Find a better way
        gvn.add_work(old);      // Lost a use, so recompute live
        if( old instanceof UnresolvedNode )
          gvn.add_work_defs(old);
        // Fold stores into NewNodes, requires no extra uses
        if( old instanceof OProjNode && old.in(0) instanceof NewNode && old._uses._len<=2 )
          for( Node use : old._uses ) if( use instanceof StoreNode ) gvn.add_work(use);
        if( old.is_mem() ) {
          Node nn = old.get_mem_writer();
          if( nn instanceof NewNode ) {
            Node nm = ProjNode.proj(nn,0);
            Node msp = nm == null ? null : nm.get_mem_writer();
            if( msp instanceof MemSplitNode )
              gvn.add_work(((MemSplitNode)msp).join());
          } else if( nn instanceof MemJoinNode || nn instanceof MrgProjNode ) gvn.add_work(nn);
        }
        // Displays for FunPtrs update
        if( this instanceof ParmNode && ((ParmNode)this)._idx==0 && old instanceof FunNode ) {
          RetNode ret = ((FunNode)old).ret();
          if( ret != null && ret.funptr() != null ) gvn.add_work(ret.funptr());
        }
        // Parm memory may fold away, if no other parm needs it for sharpening
        if( this instanceof ParmNode && ((ParmNode)this)._idx!=MEM_IDX && old instanceof FunNode ) {
          ParmNode pmem = ((FunNode)old).parm(MEM_IDX);
          if( pmem != null ) gvn.add_work(pmem);
        }
        if( this instanceof ProjNode ) { // A proj dying might let an is_copy input also die
          Node x1 = old._defs.atX(((ProjNode)this)._idx);
          if( x1 != null ) gvn.add_work(x1);
        }
        // NewNodes can be captured, if no uses
        if( old instanceof ProjNode && old.in(0) instanceof NewNode ) {
          gvn.add_work(old.in(0));
          for( Node use : old._uses )
            if( use instanceof MemSplitNode )
              gvn.add_work(((MemSplitNode)use).join());// Split/Join will swallow a NewNode
            else if( use instanceof StoreNode )
              gvn.add_work(use);
        }
        if( old instanceof NewNode ) gvn.add_work(Env.DEFMEM);
        // Removing 1/2 of the split, put other half on worklist
        if( old instanceof MemSplitNode )
          gvn.add_work_uses(old);
        if( old instanceof MemJoinNode )
          for( Node use : old._uses )
            if( use.is_mem() )
              gvn.add_work(use);
        // Remove a use from a busy stacked Phi
        if( old._uses._len==1 ) {
          Node use = old._uses.at(0);
          if( use._op == OP_PHI && use != old && use.in(0) != null )
            gvn.add_work(use.in(0));
        }
      }
    }
    return this;
  }
  @SuppressWarnings("unchecked")
  public <N extends Node> N keep() { _keep++;  return (N)this; }
  @SuppressWarnings("unchecked")
  public <N extends Node> N unhook() { assert _keep > 0; _keep--;  return (N)this; }
  public void unkeep(GVNGCM gvn) {
    assert _keep > 0; _keep--;
    if( _keep==0 && _uses._len==0 ) gvn.kill(this);
    else gvn.add_work(this);
  }
  public Node pop( ) { return del(_defs._len-1); }
  public void pop(GVNGCM gvn ) { _chk(); unuse(_defs.pop(),gvn); }
  // Remove Node at idx, auto-delete and preserve order.
  public Node remove(int idx, GVNGCM gvn) { _chk(); return unuse(_defs.remove(idx),gvn); }

  // Uses.  Generally variable length; unordered, no nulls, compressed, unused trailing space
  public Ary<Node> _uses;

  Node( byte op ) { this(op,new Node[0]); }
  Node( byte op, Node... defs ) {
    _op   = op;
    _uid  = Env.GVN.uid();
    _defs = new Ary<>(defs);
    _uses = new Ary<>(new Node[1],0);
    for( Node def : defs ) if( def != null ) def._uses.add(this);
    _tvar = new TVar(this);
    _live = all_live();
  }

  // Is a primitive
  public boolean is_prim() { return GVNGCM._INIT0_CNT==0 || _uid<GVNGCM._INIT0_CNT; }

  // Make a copy of the base node, with no defs nor uses and a new UID.
  // Some variations will use the CallEpi for e.g. better error messages.
  @NotNull public Node copy( boolean copy_edges, GVNGCM gvn) {
    try {
      Node n = (Node)clone();
      n._uid = Env.GVN.uid();             // A new UID
      n._defs = new Ary<>(new Node[1],0); // New empty defs
      n._uses = new Ary<>(new Node[1],0); // New empty uses
      n._tvar = new TVar(n);
      if( copy_edges )
        for( Node def : _defs )
          n.add_def(def);
      return n;
    } catch( CloneNotSupportedException cns ) { throw new RuntimeException(cns); }
  }

  // Short string name
  String xstr() { return STRS[_op]; } // Self   short  name
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
    if( !_in ) sb.p("----");
    else _tvar._str(sb,true);

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
  private boolean is_multi_tail() { return _op==OP_PARM || _op==OP_PHI || _op==OP_PROJ || _op==OP_CPROJ || _op==OP_FP2CLO; }
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

  // Graph rewriting.  Can change defs, including making new nodes - but if it
  // does so, all new nodes will first call gvn.xform().  If gvn._opt if false,
  // not allowed to remove CFG edges (loop backedges and function-call entry
  // points have not all appeared).  Returns null if no-progress, or a better
  // version of 'this'.  The transformed graph must remain monotonic in both
  // value() and live().
  abstract public Node ideal(GVNGCM gvn, int level);

  // Compute the current best Type for this Node, based on the types of its
  // inputs.  May return Type.ALL, especially if its inputs are in error.  It
  // must be monotonic.  This is a forwards-flow transfer-function computation.
  abstract public Type value(GVNGCM.Mode opt_mode);

  // Shortcut to update self-value
  public Type xval( GVNGCM.Mode opt_mode ) { return set_val(value(opt_mode)); }
  public Type val(int idx) { return in(idx).val(); }

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
      if( use._live != TypeMem.DEAD )
        live = (TypeMem)live.meet(use.live_use(opt_mode, this)); // Make alive used fields
    live = live.flatten_fields();
    assert live==TypeMem.DEAD || live.basic_live()==all_live().basic_live();
    assert live!=TypeMem.LIVE_BOT || (val() !=Type.CTRL && val() !=Type.XCTRL);
    return live;
  }
  // Shortcut to update self-live
  public void xliv( GVNGCM.Mode opt_mode ) { _live = live(opt_mode); }
  // Compute local contribution of use liveness to this def.
  // Overridden in subclasses that do per-def liveness.
  public TypeMem live_use( GVNGCM.Mode opt_mode, Node def ) {
    return _keep>0 ? TypeMem.MEM : _live;
  }

  // Default lower-bound liveness.  For control, its always "ALIVE" and for
  // memory opts (and tuples with memory) its "ALL_MEM".
  public TypeMem all_live() { return TypeMem.LIVE_BOT; }
  // We have a 'crossing optimization' point: changing the pointer input to a
  // Load or a Scope changes the memory demanded by the Load or Scope.  Same:
  // changing a def._type changes the use._live, requiring other defs to be
  // revisited.  For Calls, changing the input function type to something low
  // means the call can resolve it - unresolved fptrs are not live.
  public boolean input_value_changes_live() { return _op==OP_SCOPE || _op==OP_LOAD || _op==OP_CALLEPI || _op==OP_TYPE; }
  public boolean value_changes_live() { return _op==OP_CALL; }
  public boolean live_changes_value() { return false; }


  // Hindley-Milner inspired typing, or CNC Thesis based congruence-class
  // typing.
  @Override public int uid() { return _uid; }

  // Return any type error message, or null if no error
  public ErrMsg err( boolean fast ) { return null; }

  // Operator precedence is only valid for binary functions.
  // 1-9: Normal precedence
  // 0  : Balanced op; precedence is from Parse.term() and not expr().
  // -1 : Invalid
  // -2 : Forward ref.
  public byte op_prec() { return -1; }

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
    if( _defs._len != n._defs._len ) return false;
    // Note pointer-equality
    for( int i=0; i<_defs._len; i++ ) if( _defs._es[i] != n._defs._es[i] ) return false;
    return true;
  }

  // Forward reachable walk, setting types to all_type().dual() and making all dead.
  public final void walk_initype( GVNGCM gvn, VBitSet bs ) {
    if( bs.tset(_uid) ) return;    // Been there, done that
    set_val(Type.ANY);             // Highest value
    _live = TypeMem.DEAD;          // Not alive
    // Walk reachable graph
    gvn.add_work(this);
    for( Node use : _uses ) use.walk_initype(gvn,bs);
    for( Node def : _defs ) if( def != null ) def.walk_initype(gvn,bs);
  }

  // Assert all ideal, value and liveness calls are done
  public final boolean more_ideal(GVNGCM gvn, VBitSet bs, int level) {
    if( bs.tset(_uid) ) return false; // Been there, done that
    if( _keep == 0 && _live.is_live() ) { // Only non-keeps, which is just top-level scope and prims
      Node idl = ideal(gvn,level);
      if( idl != null )
        return true;            // Found an ideal call
      Type t = value(gvn._opt_mode);
      if( oval() != t )
        return true;            // Found a value improvement
      TypeMem live = live(gvn._opt_mode);
      if( _live != live )
        return true;            // Found a liveness improvement
    }
    for( Node def : _defs ) if( def != null && def.more_ideal(gvn,bs,level) ) return true;
    for( Node use : _uses ) if( use != null && use.more_ideal(gvn,bs,level) ) return true;
    return false;
  }
  // Assert all value and liveness calls only go forwards.  Returns >0 for failures.
  public final int more_flow(GVNGCM gvn, VBitSet bs, boolean lifting, int errs) {
    if( bs.tset(_uid) ) return errs; // Been there, done that
    // Check for only forwards flow, and if possible then also on worklist
    Type    oval= oval(), nval = value(gvn._opt_mode);
    TypeMem oliv=_live  , nliv = live (gvn._opt_mode);
    if( nval != oval || nliv != oliv ) {
      boolean ok = lifting
        ? nval.isa(oval) && nliv.isa(oliv)
        : oval.isa(nval) && oliv.isa(nliv);
      if( !ok || (!gvn.on_work(this) && _keep==0) ) { // Still-to-be-computed?
        bs.clear(_uid);                     // Pop-frame & re-run in debugger
        System.err.println(dump(0,new SB(),true)); // Rolling backwards not allowed
        errs++;
      }
    }
    for( Node def : _defs ) if( def != null ) errs = def.more_flow(gvn,bs,lifting,errs);
    for( Node use : _uses ) if( use != null ) errs = use.more_flow(gvn,bs,lifting,errs);
    return errs;
  }

  // Gather errors, walking from Scope to START.
  public void walkerr_def( HashSet<ErrMsg> errs, VBitSet bs ) {
    if( bs.tset(_uid) ) return; // Been there, done that
    for( int i=0; i<_defs._len; i++ ) {
      Node def = _defs.at(i);   // Walk data defs for more errors
      if( def == null || def.val() == Type.XCTRL ) continue;
      // Walk function bodies that are wired, but not bare FunPtrs.
      if( def instanceof FunPtrNode && !def.is_forward_ref() )
        continue;
      def.walkerr_def(errs,bs);
    }
    if( is_prim() ) return;
    // Skip reporting if any input is 'all', as the input should report instead.
    for( Node def : _defs )
      if( def !=null && def.val() ==Type.ALL )
        return;                 // Skip reporting.
    adderr(errs);
  }

  private void adderr( HashSet<ErrMsg> errs ) {
    ErrMsg msg = err(false);
    if( msg==null ) return;
    msg._order = errs.size();
    errs.add(msg);
  }
  @Override public boolean is_dead() { return _uses == null; }
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
  // with a TypeMem at(1).
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
  public Type sharptr( Node mem ) { return mem.val().sharptr(val()); }

  // Aliases that a MemJoin might choose between.  Not valid for nodes which do
  // not manipulate memory.
  BitsAlias escapees() { throw com.cliffc.aa.AA.unimpl("graph error"); }

  // Walk a subset of the dominator tree, looking for the last place (highest
  // in tree) this predicate passes, or null if it never does.
  Node walk_dom_last(Predicate<Node> P) {
    assert in(0) != null;       // All default control nodes pass ctrl in slot 0
    Node n = in(0).walk_dom_last(P);
    if( n != null ) return n;   // Take last answer first
    return P.test(this) ? this : null;
  }


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
    public static ErrMsg forward_ref(Parse loc, FunNode fun) { return forward_ref(loc,fun._name); }
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
