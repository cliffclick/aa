package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.util.Ary;

// Global Value Numbering, Global Constant Propagation
public class GVNGCP {
  final boolean _opt; // Optimistic (types start at ANY and fall to ALL) or pessimistic (start ALL lifting to ANY)
  
  // Iterative worklist
  Ary<Node> _work = new Ary<>(new Node[1],0);

  // Array of types representing current node types.  Essentially a throw-away
  // temp extra field on Nodes.
  Ary<Type> _ts = new Ary<>(new Type[1],0);

  GVNGCP( boolean opt ) {
    _opt = opt;
    for( UnresolvedNode unr : Env.top()._par._refs.values() ) {
      for( Node n : unr._defs ) setype(n,n.value(this));
      setype(unr,unr.value(this));
    }
  }

  public Type type( Node n ) {
    Type t = _ts.at(n._uid);
    assert t!=null;
    return t;
  }
  public Type setype( Node n, Type t ) {
    assert t != null;
    return _ts.set(n._uid,t);
  }

  // Apply graph-rewrite rules to Node n; if anything changes put all users of
  // n on the worklist for further eval.
  public Node xform( Node n ) {
    Node x = xform0(n);
    if( x == null ) return n;
    // Change!  Add users of n to the worklist, as well as point them to x
    while( n._uses._len > 0 ) {
      Node u = n._uses.del(0);
      _work.add(u);
      int ux = u._defs.find(a -> a==n);
      u._defs.set(ux,x); // was n now x
      x.add_use(u);
    }
    return x;
  }
  private Node xform0( Node n ) {
    assert n!=null;
    int cnt=0;                  // Progress bit
    // Try generic graph reshaping
    Node x=n;  
    for( Node y = n; y!=null; y = x.ideal(this) ) {
      x=y;
      cnt++; assert cnt < 1000;
    }
    
    // Make sure some type exists in the table... before calling
    // Value which might recursively ask for its own type
    if( x._uid >= _ts._len ) _ts.set(x._uid,x.all_type()); // Set it in
    // Get best type
    Type t = x.value(this);
    if( t != _ts.at(x._uid) ) { // Got a new type
      _ts.set(x._uid,t);        // Set it in
      x.lift_type(t);           // Some nodes can cache a local type directly
      cnt++;
    }
    
    if( t.is_con() && !(x instanceof ConNode) ) {
      setype(x = new ConNode(t),t);
      cnt++;
    }

    // GVN goes here
    
    return cnt<=1 ? null : x;
  }
}
