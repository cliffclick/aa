package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.util.Ary;

import java.util.HashMap;

// Global Value Numbering, Global Constant Propagation
public class GVNGCP {
  private final boolean _opt; // Optimistic (types start at ANY and fall to ALL) or pessimistic (start ALL lifting to ANY)
  
  // Iterative worklist
  private Ary<Node> _work = new Ary<>(new Node[1],0);

  // Array of types representing current node types.  Essentially a throw-away
  // temp extra field on Nodes.  It is either bottom-up, conservatively correct
  // or top-down and optimistic.
  private Ary<Type> _ts = new Ary<>(new Type[1],0);

  // Global expressions, to remove redundant Nodes
  private HashMap<Node,Node> _vals = new HashMap<>();
  
  GVNGCP( boolean opt ) { _opt = opt; }

  public Type type( Node n ) {
    Type t = n._uid < _ts._len ? _ts._es[n._uid] : null;
    if( t != null ) return t;
    t = n.all_type();           // If no type yet, defaults to the pessimistic type
    if( _opt ) t = t.dual();
    return _ts.set(n._uid,t);
  }
  private void setype( Node n, Type t ) {
    assert t != null;
    _ts.set(n._uid,t);
  }

  // Make globally shared common ConNode for this type.
  Node con( Type t ) {
    Node con = new ConNode<>(t);
    Node con2 = _vals.get(con);
    if( con2 != null ) return con2; // TODO: con goes dead, should be recycled
    setype(con,t);
    _vals.put(con,con);
    return con;
  }

  // Record a Node, but do not optimize it for value and ideal calls, as it is
  // mid-construction from the parser.  Any function call with yet-to-be-parsed
  // call sites, and any loop top with an unparsed backedge needs to use this.
  public Node init( Node n ) {
    assert n._uses._len==0;
    setype(n,n.all_type());
    return n;
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
      cnt++;
    }
    
    if( t.is_con() && !(x instanceof ConNode) ) {
      setype(x = new ConNode<>(t),t);
      cnt++;
    }

    // GVN goes here
    
    return cnt<=1 ? null : x;
  }
}
