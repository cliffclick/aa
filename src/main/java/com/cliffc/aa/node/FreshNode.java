package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeNil;

// "fresh" the incoming TVar: make a fresh instance before unifying
public class FreshNode extends Node {
  // The "non-generative" set is the variables which are NOT type polymorphic.
  // This includes all lambda arguments inside the lambda, plus any
  // variables used mid-definition.  The only variables used mid-definition are
  // forward-refs.
  public TV3[] _nongen;   // Set of visible non-generative type vars

  // Asking for a non-gen of self; never makes a fresh
  private final boolean _copy;

  public FreshNode( Node id, Env e ) {
    super(id);
    // Copy the set of NONGEN variables in the current lexical tree
    boolean copy = false;
    for( ; e!=null; e=e._par ) {
      StructNode stk = e._scope.stk();
      for( int i=0; i<stk._nargs; i++ ) {
        if( stk.in(i)==id )
          copy=true;
        addDef(stk.in(i));
      }
    }
    _copy = copy;
  }
  public FreshNode( Node id ) {
    super(id);
    _copy=false;
  }

  @Override public String label() { return "Fresh"; }
  public Node id() { return in(0); } // The HM identifier
  public static Node peek(Node f) { return f instanceof FreshNode fsh ? fsh.id() : f; }
  @Override public boolean shouldCon() { return id().shouldCon(); }

  @Override public Type value() { return id()._val; }

  @Override public Type live_use( int i ) {
    if( i==0 ) return _live;    // Pass full liveness along
    return Type.ALL;            // Basic aliveness for nongen set
  }

  @Override public Node ideal_reduce() {
    // Not a TFP, so toss it
    if( _val.isCon() && !(_val instanceof TypeFunPtr) )
      return _val==TypeNil.XNIL ? new ConNode(_val).init() : id();

    if( _copy )
      return id();
    return null;
  }

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    unelock();                  // Adding a tvar changes equals
    TV3 tv = _tvar = new TVLeaf();
    tv.deps_add_deep(this);
    _nongen = new TV3[len()-1];
    for( int i = 1; i < len(); i++ )
      _nongen[i-1] = in(i).set_tvar();
    return tv;
  }

  @Override public boolean unify( boolean test ) {
    TV3 fresh = id().tvar(), that = tvar();
    return fresh.fresh_unify(_nongen,that,test);
  }
  // Two FreshNodes are only equal, if they have compatible TVars
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FreshNode frsh) ) return false;
    return (_tvar!=null && frsh._tvar!=null && tvar()==frsh.tvar()); // Pre-combo, must be the same Node
  }
}
