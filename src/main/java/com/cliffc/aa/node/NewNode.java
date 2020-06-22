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
  // TypeObj.UNUSE for dead allocations.
  TypeObj _defmem;

  // Just TMP.make(_alias,OBJ)
  public TypeMemPtr _tptr;

  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  public final static int CUTOFF=2; // Depth of types before we start forcing approximations

  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewNode( byte type, int parent_alias, T to, Node ctrl         ) { super(type,ctrl    ); _init(parent_alias,to); }
  public NewNode( byte type, int parent_alias, T to, Node ctrl,Node fld) { super(type,ctrl,fld); _init(parent_alias,to); }
  private void _init(int parent_alias, T to) {
    _alias = BitsAlias.new_alias(parent_alias);
    sets(to,null);
    _tptr = TypeMemPtr.make(_alias,TypeObj.OBJ);
  }
  String xstr() { return "New*"+_alias; } // Self short name
  String  str() { return "New"+_ts; } // Inline less-short name

  static int def_idx(int fld) { return fld+1; } // Skip ctrl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#

  // Recompute default memory cache on a change
  @SuppressWarnings("unchecked")
  protected final void sets( T ts, GVNGCM gvn ) {
    _ts = ts;
    TypeObj olddef = _defmem;
    _defmem = (T)ts.crush();
    if( gvn!=null ) {
      gvn.add_work_uses(this);
      if( olddef != _defmem )
        gvn.add_work(Env.DEFMEM);
    }
  }

  @SuppressWarnings("unchecked")
  @Override public Node ideal(GVNGCM gvn, int level) {
    // If either the address or memory is not looked at then the memory
    // contents are dead.  The object might remain as a 'gensym' or 'sentinel'
    // for identity tests.
    if( _defs._len > 1 && captured(gvn) ) {
      while( !is_dead() && _defs._len > 1 )
        pop(gvn);               // Kill all fields
      if( is_dead() ) return this;
      _ts = dead_type();
      _defmem = TypeObj.UNUSED;
      gvn.add_work_uses(_uses.at(0));  // Get FPtrs from OProj from this
      return this;
    }
    return null;
  }
  abstract T dead_type();
  @Override public boolean basic_liveness() { return true; }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return def==in(0) ? TypeMem.ALIVE : TypeMem.ESCAPE; }
  
  // Basic escape analysis.  If no escapes and no loads this object is dead.
  private boolean captured( GVNGCM gvn ) {
    if( _keep > 0 ) return false;
    if( _uses._len==0 ) return false; // Dead or being created
    Node mem = _uses.at(0);
    // If only either address or memory remains, then memory contents are dead
    if( _uses._len==1 ) {
      if( mem instanceof OProjNode ) return true; // No pointer, just dead memory
      // Just a pointer; currently on Strings become memory constants and
      // constant-fold - leaving the allocation dead.
      return !(gvn.type(in(1)) instanceof TypeStr);
    }
    Node ptr = _uses.at(1);
    if( ptr instanceof OProjNode ) ptr = _uses.at(0); // Get ptr not mem
    // Scan for pointer-escapes.  Really stupid: allow if-nil-check and if-eq-check only.
    for( Node use : ptr._uses )
      if( !(use instanceof IfNode) )
        return false;
    // No escape, no loads, so object is dead
    return true;
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
}
