package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.tvar.TVExpanding;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeNil;

// "fresh" the incoming TVar: make a fresh instance before unifying
public class FreshNode extends Node {
  private TV3[] _nongen;        // Set of visible non-generative type vars
  
  public FreshNode( Node id, Env e ) {
    super(OP_FRESH, id);
    // Copy the set of NONGEN variables
    for( ; e!=null; e=e._par ) {
      StructNode stk = e._scope.stk();
      for( int i=0; i<stk._nargs; i++ )
        add_def(stk.in(i));
    }
  }

  public Node id() { return in(0); } // The HM identifier
  public static Node peek(Node f) { return f instanceof FreshNode fsh ? fsh.id() : f; }

  @Override public Type value() { return id()._val; }

  @Override public Type live_use(Node def ) {
    if( def==id() ) return _live; // Pass full liveness along
    return Type.ALL;              // Basic aliveness for control
  }

  @Override public Node ideal_reduce() {
    // Not a TFP, so toss it
    if( _val.is_con() && !(_val instanceof TypeFunPtr) )
      return _val==TypeNil.XNIL ? new ConNode(_val).init() : id();

    return null;
  }

  // The "non-generative" set is the variables which are NOT type polymorphic.
  // This includes all lambda arguments inside the lambda, plus any
  // variables used mid-definition.  The only variables used mid-definition are
  // forward-refs.
  TV3[] nongen() { return _nongen; }

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    unelock();                  // Adding a tvar changes equals
    TV3 tv = _tvar = new TVLeaf();
    tv.deps_add_deep(this);
    if( len()>1 ) {
      _nongen = new TV3[len() - 1];
      for( int i = 1; i < len(); i++ )
        _nongen[i - 1] = in(i).set_tvar();
      TV3 id = id().set_tvar();
      if( id instanceof TVExpanding tex )
        tex.make_nongen_delay(tv,_nongen,this);
    }
    return tv;
  }
    
  @Override public boolean unify( boolean test ) {
    TV3 fresh = id().tvar(), that = tvar();
    return fresh.fresh_unify(this,that,nongen(),test);
  }
  // Two FreshNodes are only equal, if they have compatible TVars
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FreshNode frsh) ) return false;
    return (_tvar!=null && frsh._tvar!=null && tvar()==frsh.tvar()); // Pre-combo, must be the same Node
  }
}
