package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.util.Ary;

import java.util.BitSet;
import java.util.HashMap;

// Global Value Numbering, Global Code Motion
public class GVNGCP {
  private final boolean _opt; // Optimistic (types start at ANY and fall to ALL) or pessimistic (start ALL lifting to ANY)

  // Unique dense node-numbering
  private int CNT;
  BitSet _live = new BitSet();
  public int uid() { _live.set(CNT); return CNT++; }

  // Iterative worklist
  private Ary<Node> _work = new Ary<>(new Node[1],0);
  private BitSet _wrk_bits = new BitSet();

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
    if( con2 != null ) { kill0(con); return con2; } // TODO: con goes dead, should be recycled
    setype(con,t);
    _vals.put(con,con);
    return con;
  }

  // Record a Node, but do not optimize it for value and ideal calls, as it is
  // mid-construction from the parser.  Any function call with yet-to-be-parsed
  // call sites, and any loop top with an unparsed backedge needs to use this.
  Node init( Node n ) {
    assert n._uses._len==0;
    setype(n,n.all_type());
    _vals.put(n,n);
    return n;
  }
  
  // Apply graph-rewrite rules to Node n; if anything changes put all users of
  // n on the worklist for further eval.
  public Node xform( Node n ) {
    Node x = xform0(n);
    if( x == null ) return n;
    // Change!  Add users of n to the worklist
    assert n._uses != null;
    for( Node u : n._uses )
      if( !_wrk_bits.get(u._uid) ) { _wrk_bits.set(u._uid);  _work.add(u);  }
    if( x == n ) return n;
    // Complete replacement; point uses to x.
    while( n._uses._len > 0 ) {
      Node u = n._uses.del(0);
      u._defs.set(u._defs.find(a -> a==n),x); // was n now x
      x._uses.add(u);
    }
    kill0(n);
    return x;
  }
  /** Look for a better version of 'n'.  Can change n's defs via the ideal()
   *  call, including making new nodes.  'n' will exist on exit and n's uses
   *  are left untouched.
   *  @param n Node to be idealized
   *  @return null for no-change, or a better version of n */
  private Node xform0( Node n ) {
    assert n!=null;
    int cnt=0;                  // Progress bit
    // Try generic graph reshaping, looping till no-progress.
    Node x=n;  
    for( Node y = n; y!=null; y = x.ideal(this) ) {
      x=y;
      cnt++; assert cnt < 1000;
    }
    
    // Make sure some type exists in the table... before calling
    // Value which might recursively ask for its own type
    if( x._uid >= _ts._len ) _ts.set(x._uid,x.all_type()); // Set it in
    Type t = x.value(this);     // Get best type
    if( t != _ts.at(x._uid) ) { // Got a new type
      _ts.set(x._uid,t);        // Set it in
      cnt++;
    }
    
    if( t.is_con() && !(x instanceof ConNode) ) {
      setype(x = new ConNode<>(t),t);
      cnt++;
    }

    // GVN
    Node y = _vals.get(x);
    if( y != x ) {
      if( y != null ) { x = y; cnt++; }
      else _vals.put(x, x);
    }

    return cnt<=1 ? null : x;
  }
  // Recursively kill off a dead node, which might make lots of other nodes go dead
  public void kill( Node n ) {
    Node xn = _vals.remove(n);
    assert xn == n;             // Should have been in table to be removed
    kill0(n);
  }
  // Version for never-GVN'd; common for e.g. constants to die early or
  // RootNode, and some other make-and-toss Nodes.
  public void kill0( Node n ) {
    if( n._uid < _ts._len ) _ts._es[n._uid] = null;
    assert n._uses._len==0;
    for( int i=0; i<n._defs._len; i++ )
      n.set_def(i,null,this);   // Recursively destroy dead nodes
    n._defs = n._uses = null;   // Poor-mans indication of a dead node, probably needs to recycle these...
    _live.clear(n._uid);
    if( n._uid==CNT )
      throw AA.unimpl();
  }
}
