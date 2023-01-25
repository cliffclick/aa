package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.tvar.TVPtr;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

// Allocates memory for the input
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.
//
// Takes in a Control (often null), a Memory, and a TypeStruct producer (ala StructNode).
// Produces a Tuple of (TypeMem,TypeMemPtr).
public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias; // Alias class
  private final int _reset0_alias; // Reset, if PrimNode aliases split & moved
  // Alias is dead for all time
  private boolean _killed;

  // Just TMP.make(_alias,ISUSED)
  public TypeMemPtr _tptr;

  public NewNode( int alias ) {
    super(OP_NEW);
    _reset0_alias = alias;       // Allow a reset, if this alias splits and then we want to run a new test
    set_alias( alias);
  }
  public NewNode( ) { this(BitsAlias.new_alias()); }

  private void set_alias(int alias) {
    if( _elock ) unelock();    // Unlock before changing hash
    _alias = alias;
    _tptr = TypeMemPtr.make(alias,TypeStruct.ISUSED);
  }
  @Override public String xstr() { return "New"+"*"+_alias; } // Self short name
  @Override void walk_reset0() { assert is_prim(); set_alias(_reset0_alias); }

  @Override public Type value() { return _killed ? _tptr.dual() : _tptr; }
  
  @Override public Node ideal_reduce() {
    if( !used() && !_killed ) {
      _killed = true;
      RootNode.kill_alias(_alias);
      Env.GVN.add_reduce_uses(this);
      Env.GVN.add_flow(this);
      return this;
    }
    return null;
  }
  
  // If all uses do not escape the pointer, the New is dead.
  private boolean used() {
    if( is_prim() ) return true;
    for( Node use : _uses )
      if( !(use instanceof StoreNode st) || st.rez()==this )
        return true;
    return false;
  }
  
  @Override public boolean has_tvar() { /*assert used(); */ return true; }

  @Override public TV3 _set_tvar() { return new TVPtr(new TVLeaf()); }

  // clones during inlining all become unique new sites
  @Override public @NotNull NewNode copy(boolean copy_edges) {
    // Split the original '_alias' class into 2 sub-aliases
    NewNode nnn = (NewNode)super.copy(copy_edges);
    nnn.set_alias(BitsAlias.new_alias(_alias)); // Children alias classes, split from parent
        set_alias(BitsAlias.new_alias(_alias)); // The original NewNode also splits from the parent alias
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }


  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  @Override public boolean equals(Object o) {  return this==o; }
}
