package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.function.Predicate;

// Sea-of-Nodes
public abstract class Node implements Cloneable {
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
  static final byte OP_LIBCALL=12;
  static final byte OP_LOAD   =13;
  static final byte OP_MERGE  =14;
  static final byte OP_NAME   =15; // Cast a prior NewObj to have a runtime Name
  static final byte OP_NEWOBJ =16; // Allocate a new struct
  static final byte OP_NEWSTR =17; // Allocate a new string (array)
  static final byte OP_PARM   =18;
  static final byte OP_PHI    =19;
  static final byte OP_PRIM   =20;
  static final byte OP_PROJ   =21;
  static final byte OP_REGION =22;
  static final byte OP_RET    =23;
  static final byte OP_SCOPE  =24;
  static final byte OP_START  =25;
  static final byte OP_STMEM  =26;
  static final byte OP_STORE  =27;
  static final byte OP_TMP    =28;
  static final byte OP_TYPE   =29;
  static final byte OP_UNR    =30;
  static final byte OP_MAX    =31;

  private static final String[] STRS = new String[] { null, "Call", "CallEpi", "Cast", "Con", "CProj", "DefMem", "Err", "FP2Clo", "Fun", "FunPtr", "If", "LibCall", "Load", "Merge", "Name", "NewObj", "NewStr", "Parm", "Phi", "Prim", "Proj", "Region", "Return", "Scope", "Start", "StartMem", "Store", "Tmp", "Type", "Unresolved" };

  public int _uid;  // Unique ID, will have gaps, used to give a dense numbering to nodes
  final byte _op;   // Opcode (besides the object class), used to avoid v-calls in some places
  public byte _keep;// Keep-alive in parser, even as last use goes away
  public TypeMem _live; // Liveness; assumed live in gvn.iter(), assumed dead in gvn.gcp().

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
      if( old._uses._len==0 && old._keep==0 ) gvn.kill(old); // Recursively begin deleting
      if( !old.is_dead() ) {
        // TODO: Find a better way
        gvn.add_work(old);      // Lost a use, so recompute live
        if( old instanceof UnresolvedNode )
          gvn.add_work_defs(old);
        // Fold stores into NewNodes, requires no extra uses
        if( old instanceof OProjNode && old.in(0) instanceof NewNode && old._uses._len<=2 )
          gvn.add_work_uses(old);
        if( this instanceof ParmNode && ((ParmNode)this)._idx==0 && old instanceof FunNode ) {
          RetNode ret = ((FunNode)old).ret();
          if( ret != null ) gvn.add_work(ret.funptr());
        }
        if( this instanceof ParmNode && ((ParmNode)this)._idx!=-2 && old instanceof FunNode ) {
          ParmNode pmem = ((FunNode)old).parm(-2);
          if( pmem != null ) gvn.add_work(pmem);
        }
        if( old instanceof ProjNode && old.in(0) instanceof NewNode )
          gvn.add_work(old.in(0));
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
  public void remove(int idx, GVNGCM gvn) { _chk(); unuse(_defs.remove(idx),gvn); }

  // Uses.  Generally variable length; unordered, no nulls, compressed, unused trailing space
  public Ary<Node> _uses;

  Node( byte op ) { this(op,new Node[0]); }
  Node( byte op, Node... defs ) {
    _op   = op;
    _uid  = Env.GVN.uid();
    _defs = new Ary<>(defs);
    _uses = new Ary<>(new Node[1],0);
    for( Node def : defs ) if( def != null ) def._uses.add(this);
    _live = basic_liveness() ? TypeMem.EMPTY : TypeMem.ALLMEM;
   }

  // Is a primitive
  public boolean is_prim() { return GVNGCM._INIT0_CNT==0 || _uid<GVNGCM._INIT0_CNT; }

  // Make a copy of the base node, with no defs nor uses and a new UID.
  // Some variations will use the CallEpi for e.g. better error messages.
  @NotNull Node copy( boolean copy_edges, GVNGCM gvn) {
    try {
      Node n = (Node)clone();
      n._uid = Env.GVN.uid();             // A new UID
      n._defs = new Ary<>(new Node[1],0); // New empty defs
      n._uses = new Ary<>(new Node[1],0); // New empty uses
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
    sb.p(str());
    Type t = Env.GVN.self_type(this);
    sb.s().p(t==null ? "----" : t.toString());
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
  boolean is_multi_head() { return _op==OP_CALL || _op==OP_CALLEPI || _op==OP_FUN || _op==OP_IF || _op==OP_LIBCALL || _op==OP_NEWOBJ || _op==OP_NEWSTR || _op==OP_REGION || _op==OP_START; }
  private boolean is_multi_tail() { return _op==OP_PARM || _op==OP_PHI || _op==OP_PROJ || _op==OP_CPROJ || _op==OP_FP2CLO; }
  private boolean is_CFG()        { return _op==OP_CALL || _op==OP_CALLEPI || _op==OP_FUN || _op==OP_RET || _op==OP_IF || _op==OP_REGION || _op==OP_START || _op==OP_CPROJ || _op==OP_SCOPE; }

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
      // Walk the CFG, walking a CallEpi very last
      Node cepi = null;
      for( Node use : _uses )
        if( use instanceof CallEpiNode ) cepi = use;
        else if( use.is_CFG() ) use.postorder(nodes,bs);
      if( cepi != null ) cepi.postorder(nodes,bs);
    }

    // Walk the rest (especially data).  Since visit bit set on the CFGs its OK
    // to walk them also.  Calls are special, since their Proj's feed into a
    // Fun's Parms.  We want the Fun to walk its own Parms, in order so ignore
    // these edges.  Since the Parms are all reachable from the Fun they get
    // walked eventually.
    if( _op != OP_CALL && _op!=OP_RET )
      for( Node use : _uses )
        use.postorder(nodes,bs);

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
  abstract public Type value(GVNGCM gvn);

  // Compute the current best liveness for this Node, based on the liveness of
  // its uses.  If basic_liveness(), returns a simple DEAD/EMPTY.  Otherwise
  // computes the alive memory set down to the field level.  May return
  // TypeMem.FULL, especially if its uses are of unwired functions.
  // It must be monotonic.
  // This is a reverse-flow transfer-function computation.
  public TypeMem live( GVNGCM gvn) {
    if( basic_liveness() ) {    // Basic liveness only; e.g. primitive math ops
      for( Node use : _uses )   // Computed across all uses
        if( use._live != TypeMem.DEAD )
          return TypeMem.EMPTY; // Report basic liveness only
      return TypeMem.DEAD;
    }
    // Compute meet/union of all use livenesses
    TypeMem live = TypeMem.DEAD; // Start at lattice top
    for( Node use : _uses )      // Computed across all uses
      live = (TypeMem)live.meet(use.live_use(gvn, this)); // Make alive used fields
    return live;
  }
  // Compute local contribution of use liveness to this def.
  // Overridden in subclasses that do per-def liveness.
  public TypeMem live_use( GVNGCM gvn, Node def ) {
    return _keep>0 ? TypeMem.MEM : _live;
  }
  // Compute basic liveness only: a boolean flag of alive-or-dead represented
  // as TypeMem.DEAD or TypeMem.EMPTY.
  public boolean basic_liveness() { return true; }
  // We have a 'crossing optimization' point: changing the pointer input to a
  // Load or a Scope changes the memory demanded by the Load or Scope.  Same:
  // changing a def._type changes the use._live, requiring other defs to be
  // revisited.  For Calls, changing the input function type to something low
  // means the call can resolve it - unresolved fptrs are not live.
  public boolean input_value_changes_live() { return _op==OP_SCOPE || _op==OP_LOAD || _op==OP_CALLEPI || _op==OP_TYPE; }
  public boolean value_changes_live() { return _op==OP_CALL; }
  public boolean live_changes_value() { return false; }

  // Return any type error message, or null if no error
  public String err(GVNGCM gvn) { return null; }

  // Operator precedence is only valid for ConNode of binary functions
  public byte  op_prec() { return -1; }
  public byte may_prec() { return -1; }

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

  // Assert all ideal, value and liveness calls are done
  public final boolean more_ideal(GVNGCM gvn, VBitSet bs, int level) {
    if( bs.tset(_uid) ) return false; // Been there, done that
    if( _keep == 0 && _live.is_live() ) { // Only non-keeps, which is just top-level scope and prims
      Node idl = ideal(gvn,level);
      if( idl != null )
        return true;            // Found an ideal call
      Type t = value(gvn);
      if( gvn.type(this) != t )
        return true;            // Found a value improvement
      TypeMem live = live(gvn);
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
    if( _keep == 0 ) {
      Type    oval=gvn.type(this), nval = value(gvn);
      TypeMem oliv=_live         , nliv = live (gvn);
      if( nval != oval || nliv != oliv ) {
        boolean ok = lifting
          ? nval.isa(oval) && nliv.isa(oliv)
          : oval.isa(nval) && oliv.isa(nliv);
        if( !ok || !gvn.on_work(this) ) {     // Still-to-be-computed?
          bs.clear(_uid);                     // Pop-frame & re-run in debugger
          System.err.println(dump(0,new SB(),true)); // Rolling backwards not allowed
          errs++;
        }
      }
    }
    for( Node def : _defs ) if( def != null ) errs = def.more_flow(gvn,bs,lifting,errs);
    for( Node use : _uses ) if( use != null ) errs = use.more_flow(gvn,bs,lifting,errs);
    return errs;
  }

  // Gather errors; backwards reachable control uses only
  public void walkerr_use( Ary<String> errs, VBitSet bs, GVNGCM gvn ) {
    assert !is_dead();
    if( bs.tset(_uid) ) return;  // Been there, done that
    if( gvn.type(this) != Type.CTRL ) return; // Ignore non-control
    if( this instanceof ErrNode ) errs.add(((ErrNode)this)._msg); // Gather errors
    for( Node use : _uses )     // Walk control users for more errors
      use.walkerr_use(errs,bs,gvn);
  }

  // Gather errors; forwards reachable data uses only.  This is an RPO walk.
  public void walkerr_def( Ary<String> errs0, Ary<String> errs1, Ary<String> errs2, Ary<String> errs3, VBitSet bs, GVNGCM gvn ) {
    assert !is_dead();
    if( bs.tset(_uid) ) return; // Been there, done that
    if( is_uncalled(gvn) ) return; // FunPtr is a constant, but never executed, do not check for errors
    // Reverse walk: start at exit/return of graph and walk towards root/start.
    for( int i=0; i<_defs._len; i++ ) {
      Node def = _defs.at(i);   // Walk data defs for more errors
      if( def == null || gvn.type(def) == Type.XCTRL ) continue;
      def.walkerr_def(errs0,errs1,errs2,errs3,bs,gvn);
    }
    // Post-Order walk: check after walking
    String msg = err(gvn);      // Get any error
    if( msg != null ) {         // Gather errors
      Ary<String> errs;
      if( is_forward_ref() ) errs = errs0;      // Report unknown refs first
      else if( this instanceof ErrNode ) errs=errs1; // Report ErrNodes next
      // Report unresolved calls last, as some other error generally
      // triggered this one.
      else if( this instanceof UnresolvedNode ||
               (this instanceof CallNode && msg.contains("Unable to resolve")) )
        errs=errs3;
      else errs=errs2;          // Other errors (e.g. bad fields for Loads)
      if( errs.find(msg::equals) == -1 ) // Filter dups; happens due to e.g. inlining replicated busted code
        errs.add(msg);
    }
  }

  // Gather errors; forwards reachable data uses only
  // TODO: Moved error to PhiNode.err
  public void walkerr_gc( Ary<String> errs, VBitSet bs, GVNGCM gvn ) {
    if( bs.tset(_uid) ) return;  // Been there, done that
    if( is_uncalled(gvn) ) return; // FunPtr is a constant, but never executed, do not check for errors
    String msg = this instanceof PhiNode ? err(gvn) : null;
    if( msg != null ) errs.add(msg);
    for( int i=0; i<_defs._len; i++ )
      if( in(i) != null ) in(i).walkerr_gc(errs,bs,gvn);
  }
  public boolean is_dead() { return _uses == null; }
  public void set_dead( ) { _defs = _uses = null; }   // TODO: Poor-mans indication of a dead node, probably needs to recycle these...

  // Overridden in subclasses that return TypeTuple value types.  Such nodes
  // are always followed by ProjNodes to break out the tuple slices.  If the
  // node optimizes, each ProjNode becomes a copy of some other value... based
  // on the ProjNode index
  public Node is_copy(GVNGCM gvn, int idx) { return null; }

  // True if function is uncalled (but possibly returned or stored as
  // a constant).  Such code is not searched for errors.
  boolean is_uncalled(GVNGCM gvn) { return false; }

  // Only true for some RetNodes and FunNodes
  public boolean is_forward_ref() { return false; }

  // True if this Call/CallEpi pair does not read or write memory.
  // True for most primitives.  Returns the pre-call memory or null.
  Node is_pure_call() { return null; }

  // Walk a subset of the dominator tree, looking for the last place (highest
  // in tree) this predicate passes, or null if it never does.
  Node walk_dom_last(Predicate<Node> P) {
    if( this==Env.START ) return null; // Walked off the top
    assert in(0) != null;       // All default control nodes pass ctrl in slot 0
    Node n = in(0).walk_dom_last(P);
    if( n != null ) return n;   // Take last answer first
    return P.test(this) ? this : null;
  }

}
