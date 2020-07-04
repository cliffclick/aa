package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

// Allocates a TypeObj and produces a Tuple with the TypeObj and a TypeMemPtr.
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.

public abstract class NewNode<T extends TypeObj<T>> extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias; // Alias class

  // A list of field names and field-mods, folded into the initial state of
  // this NewObj.  These can come from initializers at parse-time, or stores
  // folded in.  There are no types stored here; types come from the inputs.
  public T _ts;             // Base object type, representing all possible future values

  // The memory state for Env.DEFMEM, the default memory.  All non-final fields
  // are ALL; final fields keep their value.  All field flags are moved to
  // bottom, e.g. as-if all fields are now final-stored.  Will be set to
  // TypeObj.UNUSE for never-allocated (eg dead allocations)
  TypeObj _defmem;

  // Just TMP.make(_alias,OBJ)
  public TypeMemPtr _tptr;

  // Monotonic, conservatively correct flag.  Starts true, flips once to false.
  // Only used by Load & Store addresses & If equality/nil checks.  Definitely
  // fails if transitively passed to an unknown Call.  Closures can be used by
  // FunPtrs and this is an escape.  Structs can be value-stored (and later
  // loaded) and this is an escape.
  //
  // TODO: Can be transitive thru _live tracking thru Phis & known Calls &
  // memory.
  public boolean _not_escaped;

  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  public final static int CUTOFF=2; // Depth of types before we start forcing approximations

  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewNode( byte type, int parent_alias, T to, Node mem         ) { super(type,null,mem    ); _init(parent_alias,to); }
  public NewNode( byte type, int parent_alias, T to, Node mem,Node fld) { super(type,null,mem,fld); _init(parent_alias,to); }
  private void _init(int parent_alias, T to) {
    _alias = BitsAlias.new_alias(parent_alias);
    _ts = to;
    _defmem = to==dead_type() ? TypeObj.UNUSED : to.crush();
    _tptr = TypeMemPtr.make(_alias,TypeObj.ISUSED);
  }
  String xstr() { return "New"+(_not_escaped?"":"!")+"*"+_alias; } // Self short name
  String  str() { return "New"+(_not_escaped?"":"!")+_ts; } // Inline less-short name

  Node mem() { return in(1); }
  static int def_idx(int fld) { return fld+2; } // Skip mem in slot 1
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#

  // Recompute default memory cache on a change
  @SuppressWarnings("unchecked")
  protected final void sets( T ts, GVNGCM gvn ) {
    _ts = ts;
    TypeObj olddef = _defmem;
    _defmem = ts.crush();
    if( gvn!=null ) {
      gvn.add_work_uses(this);
      if( olddef != _defmem )
        gvn.add_work(Env.DEFMEM);
    }
  }

  @SuppressWarnings("unchecked")
  @Override public Node ideal(GVNGCM gvn, int level) {
    Type tmem = gvn.type(mem());
    assert tmem instanceof TypeMem || tmem==Type.ANY || tmem==Type.ALL;
    // If either the address or memory is not looked at then the memory
    // contents are dead.  The object might remain as a 'gensym' or 'sentinel'
    // for identity tests.
    if( _defs._len > 2 && captured(gvn) ) {
      while( !is_dead() && _defs._len > 2 )
        pop(gvn);               // Kill all fields except memory
      _ts = dead_type();
      _defmem = TypeObj.UNUSED;
      did_not_escape(gvn);
      gvn.set_def_reg(Env.DEFMEM,_alias,gvn.add_work(gvn.con(_defmem)));
      if( is_dead() ) return this;
      gvn.add_work_uses(_uses.at(0));  // Get FPtrs from MProj from this
      return this;
    }

    // Scan for pointer-escapes to some unknown caller.
    // If not escaped we can bypass unknown calls.
    if( !_not_escaped && gvn._opt_mode>0 && !escaped() )
      return did_not_escape(gvn);

    return null;
  }
  // Set the no-escape flag, and push neighbors on worklist
  private Node did_not_escape(GVNGCM gvn) {
    _not_escaped=true;
    // Every CallEpi can now bypass
    for( Node use : Env.DEFMEM._uses )
      if( use instanceof CallEpiNode )
        gvn.add_work(use);
    // Stored ptrs do not escape
    for( Node def : _defs )
      if( def instanceof MProjNode && def.in(0) instanceof NewNode )
        gvn.add_work(def.in(0));
    return this;
  }


  @Override BitsAlias escapees(GVNGCM gvn) { return BitsAlias.make0(_alias); }
  abstract T dead_type();
  @Override public boolean basic_liveness() { return false; }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return _live; }

  // Basic escape analysis.  If no escapes and no loads this object is dead.
  private boolean captured( GVNGCM gvn ) {
    if( _keep > 0 ) return false;
    if( _uses._len==0 ) return false; // Dead or being created
    Node mem = _uses.at(0);
    // If only either address or memory remains, then memory contents are dead
    if( _uses._len==1 ) {
      if( mem instanceof MProjNode ) return true; // No pointer, just dead memory
      // Just a pointer; currently on Strings become memory constants and
      // constant-fold - leaving the allocation dead.
      return !(gvn.type(in(1)) instanceof TypeStr);
    }
    Node ptr = _uses.at(1);
    if( ptr instanceof MProjNode ) ptr = _uses.at(0); // Get ptr not mem

    // Scan for memory contents being unreachable.
    // Really stupid!
    for( Node use : ptr._uses )
      if( !(use instanceof IfNode) )
        return false;
    // Only used to nil-check (always not-nil) and equality (always unequal to
    // other aliases).
    return true;
  }

  private boolean escaped() {
    if( _uses._len!=2 ) return false; // Dying/dead, not escaped
    Node ptr = _uses.at(0);
    if( ptr instanceof MProjNode ) ptr = _uses.at(1); // Get ptr not mem
    for( Node use : ptr._uses ) {
      if( use instanceof LoadNode ) continue;
      if( use instanceof StoreNode )
        if( ((StoreNode)use).val()==use ) return true; // Store to memory
        else continue; // Store address
      if( use instanceof  ScopeNode ) continue;    // Scope inspects all contents but modifies none
      if( use instanceof    PhiNode ) return true; // Requires flow tracking
      if( use instanceof FunPtrNode ) return true; // Appears as display in called function - which can then escape
      if( use instanceof   CallNode ) return true; // Downward exposed Call arg
      if( use instanceof    RetNode ) return true; // Upwards  exposed return
      if( use instanceof CallEpiNode) { assert ((CallEpiNode)use).is_copy(); return true; }
      if( use instanceof    NewNode )  // Store to a specific struct
        if( ((NewNode)use)._not_escaped ) continue;
        else return true;              // Escaping if other struct does
      if( use instanceof IntrinsicNode ) continue; // Changes memory/v-table; similar to Store address
      if( use instanceof    TypeNode ) continue;   // Type-checking, read-only
      throw com.cliffc.aa.AA.unimpl(); // Handle all cases, shouldn't be too many
    }
    return false;
  }


  // clones during inlining all become unique new sites
  @SuppressWarnings("unchecked")
  @Override @NotNull public NewNode copy( boolean copy_edges, GVNGCM gvn) {
    // Split the original '_alias' class into 2 sub-aliases
    NewNode<T> nnn = (NewNode<T>)super.copy(copy_edges, gvn);
    nnn._init(_alias,_ts);      // Children alias classes, split from parent
    // The original NewNode also splits from the parent alias
    assert gvn.touched(this);
    Type oldt = gvn.unreg(this);
    _init(_alias,_ts);
    gvn.rereg(this,oldt);
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  @Override public boolean equals(Object o) {  return this==o; }
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    return _defmem == TypeObj.UNUSED && idx==0 ? mem(): null;
  }
}
