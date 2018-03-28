package com.cliffc.aa.node;

import com.cliffc.aa.*;

public class UnresolvedNode extends Node {
  // Filter out nodes in-place that are not isa t.
  // Returns a defensive copy if there remain many unresolved choices.
  // Returns null if all choices are removed.
  public Node filter( GVNGCP gvn, Type t0 ) {
    UnresolvedNode rez=null;
    for( Node n : _defs ) {     // For each choice function
      if( t0.isa(gvn.type(n)) ) { // Want to know if each actual arg isa formal arg, or not.
        if( rez==null ) rez = new UnresolvedNode();
        rez.add_def(n);
      }
    }
    if( rez != null && rez._defs._len == _defs._len )
      return this;              // No change
    return rez;                 // Hey progress; dropped some choices
  }

  // Error if Nodes are not all ConNodes.  Return their collected types.
  public TypeUnion types( ) {
    Type[] ts = new Type[_defs._len];
    for( int i=0; i<_defs._len; i++ )
      ts[i] = ((ConNode)_defs.at(i))._t;
    return TypeUnion.make(TypeTuple.make(ts),true);
  }
  
  @Override String str() { return "ANY"; }
  @Override public Node ideal(GVNGCP gvn) {
    return _defs._len==1 ? _defs.at(0) : null;
  }
  @Override public Type value(GVNGCP gvn) {
    if( _defs._len==0 ) return Type.ANY;
    if( _defs._len==1 ) return gvn.type(_defs.at(0));
    Type[] ts = types(gvn);
    return TypeUnion.make(TypeTuple.make(ts),true);
  }
  // Return a sample op_prec, but really could assert all are the same
  @Override public int op_prec() { return _defs.at(0).op_prec(); }
}
