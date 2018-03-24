package com.cliffc.aa;


import com.cliffc.aa.util.Ary;

// Global Value Numbering, Global Constant Propagation
public class GVNGCP {
  final boolean _opt;           // Optimistic (types start at ANY and fall to ALL) or pessimistic (start ALL lifting to ANY)
  
  // Iterative worklist
  Ary<Node> _work = new Ary<>(new Node[1],0);

  // Array of types representing current node types.  Essentially a throw-away
  // temp extra field on Nodes.
  Ary<Type> _ts = new Ary<>(new Type[1],0);

  GVNGCP( boolean opt ) { _opt = opt; }

  Type type( Node n ) { return _ts.at(n._uid); }

  Node ideal( Node n ) {
    Type t = n.value(this);
    if( n._uid >= _ts._len || t != _ts.at(n._uid) ) {
      _ts.set(n._uid,t);                        // Set it in
      for( Node use : n._uses ) _work.add(use); // TODO: remove dups
    }
    if( t.is_con() && !(n instanceof ConNode) )
      throw AA.unimpl();
    return n;
  }
}
