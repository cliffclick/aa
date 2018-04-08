package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.SB;

public class UnresolvedNode extends Node {
  // Passed in a list of index-0-RetNodes (Function Pointers), filter down to
  // just functions of the given argument count.  TODO: expect to filter down
  // to matching function arguments.  Return a single Node if only one exists,
  // a reduced Unresolved if the list shrinks, null if all are filtered out, or
  // the original Unr if all RetNodes match.
  public Node filter( int nargs ) {
    Node rez=null;
    for( Node n : _defs ) {     // For each choice function
      RetNode ret = (RetNode)n;
      if( ((FunNode)ret.at(2).at(0))._tf._ts._ts.length == nargs ) { // Correct argument count
        if( rez==null ) rez = n;
        else if( rez instanceof UnresolvedNode ) ((UnresolvedNode)rez).add_def(n);
        else {
          UnresolvedNode unr = new UnresolvedNode();
          unr.add_def(n);
          unr.add_def(rez);
          rez = unr;
        }
      }
    }
    if( rez != null && rez instanceof UnresolvedNode && ((UnresolvedNode)rez)._defs._len == _defs._len )
      return this;              // No change
    return rez;                 // Hey progress; dropped some choices
  }

  @Override public String toString() {
    SB sb = new SB().p("ANY(");
    boolean first=true;
    for( Node n : _defs ) { sb.p(first?"":" ").p(n==null?"_":n.at(1).str()); first=false; }
    return sb.p(")").toString();
  }
  @Override String str() { return "ANY"; }
  @Override public Node ideal(GVNGCP gvn) {
    return _defs._len==1 ? _defs.at(0) : null;
  }
  @Override public Type value(GVNGCP gvn) {
    // Error if Nodes are not all FunNodes.  Return their collected types.
    Type[] ts = new Type[_defs._len];
    for( int i=0; i<_defs._len; i++ )
      ts[i] = gvn.type((FunNode)_defs.at(i).at(2).at(0));
    return TypeUnion.make(TypeTuple.make(ts),true);
  }
  // Return a sample op_prec, but really could assert all are the same
  @Override public int op_prec() { return _defs.at(0).op_prec(); }
}
