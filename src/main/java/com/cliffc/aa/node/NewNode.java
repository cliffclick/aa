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
  T _ts;                      // Base object type
  TypeName _name;             // If named, this is the name and _ts is the base
  boolean _captured;          // False if escapes, monotonic transition to true upon capture

  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewNode( byte type, int alias, T to, Node ctrl ) {
    super(type,ctrl);
    _alias = alias;
    _ts = to;
    _name = null;
  }
  String xstr() { return "New*"+_alias; } // Self short name
  String  str() { return "New"+xs(); } // Inline less-short name

  static int def_idx(int fld) { return fld+1; } // Skip ctrl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#
  TypeObj xs() { return _name == null ? _ts : _name; }

  // Called when folding a Named Constructor into this allocation site
  void set_name( GVNGCM gvn, TypeName name ) {
    assert !name.above_center();
    // Name is a wrapper over _ts, except for alias because Name is probably a generic type.
    TypeName n2 = name.make(xs());
    assert n2._t == xs();       // wrapping exactly once
    if( gvn.touched(this) ) {
      gvn.unreg(this);
      _name = n2;
      gvn.rereg(this,value(gvn));
    } else {
      _name = n2;
    }
  }

  @Override public Node ideal(GVNGCM gvn) {
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.
    if( captured() ) {
      boolean progress=false;
      for( int i=1; i<_defs._len; i++ )
        if( in(i)!=null ) {
          set_def(i,null,gvn);
          progress=true;
          if( is_dead() ) break;
        }
      return progress ? this : null;
    }
    return null;
  }

  // Produces a TypeMemPtr
  @Override public Type value(GVNGCM gvn) {
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.  Since this can happen DURING opto (when a call resolves)
    // and during iter, "freeze" the value in-place.  It will DCE shortly.
    return _captured ? gvn.self_type(this) : all_type();
  }

  // Basic escape analysis.  If no escapes and no loads this object is dead.
  // TODO: A better answer is to put escape analysis into the type flows.
  boolean captured( ) {
    if( _keep > 0 ) return false;
    if( _captured ) return true; // Already flagged
    if( _uses._len==0 ) return false; // Dead or being created
    Node ptr = _uses.at(0);
    if( _uses._len==1 )
      if( ptr instanceof OProjNode ) return (_captured = true);
      else return false;   // ptr being used for eq equiv tests as a unique gensym, or dying
    if( ptr instanceof OProjNode ) ptr = _uses.at(1); // Get ptr not mem
    // Scan for pointer-escapes
    for( Node use : ptr._uses ) {
      if( use instanceof StoreNode ) {
        if( ((StoreNode)use).val()==ptr ) return false; // Pointer stored; escapes
      } else if( use instanceof  LoadNode ||            // Load, direct use, treat as escape
                 use instanceof  CallNode ||            // Call arg
                 use instanceof   NewNode ||            // Same as a store escape, can be loaded from closure
                 use instanceof ScopeNode ||            // Returned form top-level scope to REPL
                 use instanceof   PhiNode ||            // TODO: scan past phi
                 use instanceof   RetNode ) {           // Returned
        return false;                                   // Escaped
      } else {
        throw AA.unimpl();      // Unknown, sort it out
      }
    }
    // No escape, no loads, so object is dead
    return (_captured = true);
  }

  @Override public Type all_type() {
    return TypeTuple.make(xs(),TypeMemPtr.make(_alias));
  }

  // Clones during inlining all become unique new sites
  @Override @NotNull public NewNode copy( boolean copy_edges, GVNGCM gvn) {
    assert !_ts.above_center(); // Never in GCP when types are high
    // Split the original '_alias' class into 2 sub-aliases
    NewNode nnn = (NewNode)super.copy(copy_edges, gvn);
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
