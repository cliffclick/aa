package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVPtr;
import com.cliffc.aa.tvar.TVStruct;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.TODO;


// Allocates memory for the input
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.
//
// NewNodes just produce the alias, no allocation (yet).
public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias; // Alias class
  private final int _reset0_alias; // Reset, if PrimNode aliases split & moved
  // Alias is dead for all time
  private boolean _killed;

  public final String _hint;
  
  // Just TMP.make(_alias,ISUSED)
  public TypeMemPtr _tptr;

  public NewNode( String hint, int alias, boolean is_con ) {
    super();
    _reset0_alias = alias;       // Allow a reset, if this alias splits and then we want to run a new test
    set_alias(alias,is_con);
    NEWS.setX(alias,this);
    _hint = hint;
  }
  public NewNode( String hint ) { this(hint,BitsAlias.new_alias(),false); }

  @Override public String label() {
    return  (_killed ? "X" : "")+_hint+"*"+_alias;
  } 

  private void set_alias(int alias, boolean is_con) {
    unelock();                  // Unlock before changing hash
    _alias = alias;
    _tptr = TypeMemPtr.make_con(BitsAlias.make0(alias),is_con,TypeStruct.ISUSED);
  }
  @Override void walk_reset0() { set_alias(_reset0_alias,_tptr._is_con); super.walk_reset0(); }

  @Override public Type value() { return _killed ? _tptr.dual() : _tptr; }
  
  @Override public Node ideal_reduce() {
    if( !_killed && !used() ) {
      _killed = true;
      RootNode.kill_alias(_alias);
      Env.GVN.add_reduce_uses(this);
      Env.GVN.add_reduce(this);
      Env.GVN.add_flow(this);
      return this;
    }
    return null;
  }
  
  // If all uses are store addresses only, then this is a write-only memory and
  // is not used.
  private boolean used() {
    if( isPrim() ) return true;
    for( int i=0; i<nUses(); i++ )
      if( !(use(i) instanceof StoreAbs sta) ||
          ( sta instanceof StoreNode st && st.rez()==this) )
        return true;
    return false;
  }

  // If all uses are load/store addresses, then the memory does not escape and
  // loads can bypass calls.
  boolean escaped(Node dep) {
    if( isPrim() ) return true;
    for( int i=0; i<nUses(); i++ ) {
      Node use = use(i);
      if( !(use instanceof LoadNode ld ||
            (use instanceof StoreNode st && st.rez()!=this) )) {
        use.deps_add(dep);
        return true;
      }
    }
    return false;
  }
  
  @Override public boolean has_tvar() { /*assert used(); */ return true; }

  @Override public TV3 _set_tvar() {
    return new TVPtr(BitsAlias.make0(_alias), new TVStruct(true) );
  }

  // clones during inlining all become unique new sites
  @Override public @NotNull NewNode copy(boolean copy_edges) {
    // Split the original '_alias' class into 2 sub-aliases
    assert !_tptr.is_con();
    NEWS.set(_alias,null);
    NewNode nnn = (NewNode)super.copy(copy_edges);
    nnn .set_alias(BitsAlias.new_alias(_alias),false); // Children alias classes, split from parent
    this.set_alias(BitsAlias.new_alias(_alias),false); // The original NewNode also splits from the parent alias
    NEWS.setX(nnn ._alias,nnn );
    NEWS.setX(this._alias,this);
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }

  @Override int hash() { return _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  @Override public boolean equals(Object o) {  return this==o; }

  private static final Ary<NewNode> NEWS = new Ary<>(new NewNode[]{null,});
  private static int NEWS_RESET;
  public static void init0() { NEWS_RESET = NEWS.len(); }
  public static void reset_to_init0() { NEWS.set_len(NEWS_RESET); }
  public static NewNode get( int alias ) {
    NewNode nnn = NEWS.atX(alias);
    if( nnn==null ) return null;
    if( nnn._alias==alias ) return nnn;
    // Split and renumbered in FunNode inline, fixup in NEWS
    throw TODO();
  }
}
