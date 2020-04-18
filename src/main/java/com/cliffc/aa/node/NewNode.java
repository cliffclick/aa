package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

// Allocates a TypeObj and produces a Tuple with the TypeObj and a TypeMemPtr.
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.

public abstract class NewNode<T extends TypeObj> extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias;          // Alias class
  T _ts;                      // Base object type.  Can contain complex ptr types.
  boolean _captured;          // False if escapes, monotonic transition to true upon capture

  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  public final static int CUTOFF=2; // Depth of types before we start forcing approximations

  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewNode( byte type, int parent_alias, T to, Node ctrl ) {
    super(type,ctrl);
    _alias = BitsAlias.new_alias(parent_alias);
    _ts = to;
  }
  public NewNode( byte type, int parent_alias, T to, Node ctrl, Node fld ) {
    super(type,ctrl,fld);
    _alias = BitsAlias.new_alias(parent_alias);
    _ts = to;
  }
  String xstr() { return "New*"+_alias; } // Self short name
  String  str() { return "New"+_ts; } // Inline less-short name

  static int def_idx(int fld) { return fld+1; } // Skip ctrl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#

  // Called when folding a Named Constructor into this allocation site
  void set_name( T name ) { assert !name.above_center();  _ts = name; }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If either the address or memory is not looked at then the memory
    // contents are dead.  The object might remain as a 'gensym' or 'sentinel'
    // for identity tests.
    boolean old = _captured;
    if( captured(gvn) ) {
      boolean progress = !old;  // Progress if 1st time captured in any case
      for( int i=1; i<_defs._len; i++ ) {
        if( gvn.type(in(i))!=Type.XSCALAR || !(in(i) instanceof ConNode) ) {
          set_def(i,gvn.con(Type.XSCALAR),gvn);
          progress=true;         // Progress!
          if( is_dead() ) break; // Progress if any edge removed
        }
      }
      return progress ? this : null;
    }
    return null;
  }

  // Basic escape analysis.  If no escapes and no loads this object is dead.
  // TODO: A better answer is to put escape analysis into the type flows.
  boolean captured( GVNGCM gvn ) {
    if( _keep > 0 ) return false;
    if( _captured ) return true; // Already flagged
    if( _uses._len==0 ) return false; // Dead or being created
    Node ptr = _uses.at(0);
    // If only either address or memory remains, then memory contents are dead
    if( _uses._len==1 && ptr instanceof OProjNode ) return (_captured = true);
    if( _uses._len==1 && !(gvn.type(in(1)) instanceof TypeStr) )
      return (_captured = true);
    if( ptr instanceof OProjNode ) ptr = _uses.at(1); // Get ptr not mem
    // Scan for pointer-escapes.  Really stupid: allow if-nil-check and if-eq-check only.
    for( Node use : ptr._uses )
      if( !(use instanceof IfNode) )
        return false;
    // No escape, no loads, so object is dead
    return (_captured = true);
  }

  // Clones during inlining all become unique new sites
  @Override @NotNull public NewNode copy( boolean copy_edges, CallEpiNode unused, GVNGCM gvn) {
    // Split the original '_alias' class into 2 sub-aliases
    NewNode nnn = (NewNode)super.copy(copy_edges, unused, gvn);
    nnn._alias = BitsAlias.new_alias(_alias); // Children alias classes, split from parent
    // The original NewNode also splits from the parent alias
    assert gvn.touched(this);
    Type oldt = gvn.unreg(this);
    _alias = BitsAlias.new_alias(_alias);
    gvn.rereg(this,oldt);
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  @Override public boolean equals(Object o) {  return this==o; }
}
