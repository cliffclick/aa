package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeNil;

// "fresh" the incoming TVar: make a fresh instance before unifying
public class FreshNode extends Node {
  public FreshNode( FunNode fun, Node ld ) { super(OP_FRESH, fun, ld); }

  public FunNode fun() { return (FunNode)in(0); } // Enclosing function for the VStack.
  public Node id() { return in(1); } // The HM identifier
  public static Node peek(Node f) { return f instanceof FreshNode fsh ? fsh.id() : f; }

  // The "non-generative" set is the variables which are NOT type polymorphic.
  // This includes all lambda arguments inside the lambda, plus any
  // variables used mid-definition.  The only variables used mid-definition are
  // forward-refs.
  TV3[] nongen() {
    // TODO: Handle vars mid-def.  Eg. "fact = ...fact...; fact(3)".
    // The first `fact` usage is mid-def, so non-gen.
    // The 2nd `fact` is post-def so IS polymorphic.
    return fun()==null ? null : fun()._nongen;
  }

  @Override public Type value() { return id()._val; }

  @Override public Type live_use(Node def ) {
    if( def==id() ) return _live; // Pass full liveness along
    return Type.ALL;              // Basic aliveness for control
  }

  @Override public Node ideal_reduce() {
    if( _val.is_con() )
      return _val==TypeNil.XNIL ? new ConNode(_val) : id();
    return null;
  }
  
  @Override public boolean has_tvar() { return true; }
  
  @Override public boolean unify( boolean test ) {
    TV3 fresh = id().tvar();
    if( fresh instanceof TVLeaf) { // Shortcut
      fresh.deps_add_deep(this);
      return false;
    }
    return fresh.fresh_unify(tvar(),nongen(),test);
  }
  // Two FreshNodes are only equal, if they have compatible TVars
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof FreshNode frsh) ) return false;
    return _tvar==frsh._tvar ||
       (_tvar!=null && frsh._tvar!=null && tvar()==frsh.tvar()); // Pre-combo, must be the same Node
  }
}
