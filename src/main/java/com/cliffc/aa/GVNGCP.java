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

  public int uid() {
    _live.set(CNT);
    return CNT++;
  }

  // Iterative worklist
  private Ary<Node> _work = new Ary<>(new Node[1], 0);
  private BitSet _wrk_bits = new BitSet();

  private Node add_work( Node n ) {
    return _wrk_bits.get(n._uid) ? n : add_work0(n);
  }
  private Node add_work0( Node n ) {
    _work.add(n);               // These need to be visited later
    _wrk_bits.set(n._uid);
    return n;
  }

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
  public boolean touched( Node n ) { return n._uid < _ts._len && _ts._es[n._uid] != null; }

  // Make globally shared common ConNode for this type.
  public Node con( Type t ) {
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
    assert!_wrk_bits.get(n._uid);
    return add_work0(n);
  }

  // Node never seen by GVN
  boolean check_new( Node n ) {
    assert n._uses._len==0;
    assert !_wrk_bits.get(n._uid);
    assert _vals.get(n)==null;
    assert n._uid < _ts._es._len || _ts._es[n._uid]==null;
    return true;
  }

  private Node xform( Node n ) {
    if( _opt ) throw AA.unimpl();
    Node x = xform_new(n);...
  }
  // Apply graph-rewrite rules on new nodes (those with no users and kept alive
  // for the parser).  Return a node registered with GVN that is possibly "more
  // ideal" than what was before.
  private Node xform_new( Node n ) {
    assert check_new(n);
    int cnt=0;        // Progress bit

    // Try generic graph reshaping, looping till no-progress.
    while( (x = n.ideal(this)) != null ) {
      kill_n_but_not_x(n);
      assert check_new(x);
      assert cnt++ < 1000; // Catch infinite ideal-loops
    }
    // Make space in type table
    Type t = n.value(this);              // Get best type
    setype(n,t);                         // Set it in
    // TODO: If x is a TypeNode, capture any more-precise type permanently into Node
    
    // Replace with a constant, if possible
    if( t.is_con() && !(n instanceof ConNode) )
      return con(t);

    // GVN
    Node nn = _vals.putIfAbsent(n);
    return nn==null ? n : nn;
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
    x._uses.add(x);             // Self-hook, to prevent accidental deletion
    kill(n);                    // Delete the old n, and anything it uses
    x._uses.del(x._uses.find(a -> a==x)); // Remove self-hook
    return x;
  }
  /** Look for a better version of 'n'.  Can change n's defs via the ideal()
   *  call, including making new nodes.  Can replace 'n' wholly, with n's uses
   *  now pointing at the replacement.
   *  @param n Node to be idealized
   *  @return null for no-change, or a better version of n */
  private Node xform0( Node n ) {
    assert n!=null;
    Node x=n,y;       // Rename, so can see original node for debugging
    int cnt=0;        // Progress bit
    // Try generic graph reshaping, looping till no-progress.
    while( (y = x.ideal(this)) != null ) {
      add_work(x); // Could be brand-new and already removed
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

    // Replace with a constant
    if( t.is_con() && !(x instanceof ConNode) ) {
      x = new ConNode<>(t);     // Make a new constant
      y = _vals.get(x);         // See if redundant
      if( y == null ) { setype(x,t); _vals.put(x,x); }
      else { kill0(x); x=y; }
      return x;
    }

    // GVN
    y = _vals.get(x);
    if( y != x ) {
      if( y != null ) { x = y; cnt++; }
      else _vals.put(x, x);
    }
    // If progress, return the new replacement
    return cnt<=1 ? null : x;
  }

  // Once the program is complete, any time anything is on the worklist we can
  // always conservatively iterate on it.
  public void iter() {
    //while( _work._len > 0 ) {
    //  Node n = _work.pop();
    //  assert _wrk_bits.get(n._uid);
    //  _wrk_bits.clear(n._uid);
    //  if( n.is_dead() ) continue;
    //  if( n._uses._len==0 ) { kill(n); continue; }
    //  xform(n);
    //}
    throw AA.unimpl();
  }

  // Recursively kill off a dead node, which might make lots of other nodes go dead
  public void kill( Node n ) {
    boolean found = false;
    for( Node x : _vals.keySet() ) if( x._uid == n._uid ) { found=true; break; }
    assert found;               // Expected in table but not there
    Node xn = _vals.remove(n);  // Remove from table
    assert xn == n : "Hash collided with an unrelated Node"; // Should have been in table to be removed
    kill0(n);
  }
  // Version for never-GVN'd; common for e.g. constants to die early or
  // RootNode, and some other make-and-toss Nodes.
  public void kill0( Node n ) {
    assert _vals.get(n)!=n;
    if( n._uid < _ts._len ) _ts._es[n._uid] = null;
    assert n._uses._len==0;
    for( int i=0; i<n._defs._len; i++ )
      n.set_def(i,null,this);   // Recursively destroy dead nodes
    n.set_dead();               // n is officially dead now
    _live.clear(n._uid);
    if( n._uid==CNT-1 ) {       // Roll back unused node indices
      //while( !_live.get(CNT-1) ) CNT--;
    }
  }
}
