package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import java.util.BitSet;

// Sea-of-Nodes
public abstract class Node {
  static final byte OP_ROOT= 1;
  static final byte OP_CON = 2;
  static final byte OP_PRIM= 3;
  static final byte OP_UNR = 4;
  static final byte OP_FUN = 5;
  static final byte OP_PARM= 6;
  static final byte OP_RET = 7;
  static final byte OP_APLY= 8;
  static final byte OP_TMP = 9;
  
  public final int _uid=Env._gvn.uid(); // Unique ID, will have gaps, used to give a dense numbering to nodes
  public final byte _op;

  // Defs.  Generally fixed length, ordered, nulls allowed, no unused trailing space.  Zero is Control.
  public Ary<Node> _defs;
  // Add def/use edge
  public void add_def(Node n) { _defs.add(n); if( n!=null ) n._uses.add(this); }
  public Node at(int i) { return _defs._es[i]; }
  // Replace def/use edge
  public Node set_def( int idx, Node n, GVNGCP gvn ) {
    Node old = _defs._es[idx];  // Get old value
    // Add edge to new guy before deleting old, in case old goes dead and
    // recursively makes new guy go dead also
    if( (_defs._es[idx] = n) != null ) n._uses.add(this);
    if( old != null ) {
      old._uses.del(old._uses.find(a -> a==this));
      if( old._uses._len==0 ) gvn.kill(old); // Recursively begin deleting
    }
    return this;
  }
  // Return Node at idx, withOUT auto-deleting it, even if this is the last
  // use.  Used by the parser to retrieve final Nodes from tmp holders.  Does
  // NOT preserve order.
  public Node del( int idx ) {
    Node n = _defs.del(idx);
    n._uses.del(n._uses.find(a -> a==this));
    return n;
  }
  
  // Uses.  Generally variable length; unordered, no nulls, compressed, unused trailing space
  public Ary<Node> _uses = new Ary<>(new Node[1],0);  
  // Strictly add uses (no defs)
  public void add_use(Node n) {
    assert _uses != null;
    _uses.add(n); }

  Node( byte op ) { this(op,new Node[0]); }
  Node( byte op, Node... defs ) {
    _op = op;
    _defs = new Ary<>(defs);
    for( Node def : defs ) if( def != null ) def.add_use(this);
  }

  
  // Short string name
  abstract String str();
  private SB xstr(SB sb) { return sb.p(_uid).p("=").p(str()); }
  @Override public String toString() {
    SB sb = new SB().p(str()).p("(");
    boolean first=true;
    for( Node n : _defs ) { sb.p(first?"":" ").p(n==null?"_":n.str()); first=false; }
    return sb.p(")").toString();
  }
  public String toString( int d ) {
    // TODO: Recursive d-depth printing
    SB sb = xstr(new SB()).p("(");
    boolean first=true;
    for( Node n : _defs ) { sb.p(first?"":" "); if(n==null) sb.p("_"); else n.xstr(sb); first=false; }
    return sb.p(")").toString();
  }
  
  // Graph rewriting.  Can change defs, including making new nodes - but if it
  // does so, all new nodes will first call ideal().  If gvn._opt if false, not
  // allowed to remove CFG edges (loop backedges and function-call entry points
  // have not all appeared).
  // Returns null if no-progress, or better version of 'this'.
  abstract public Node ideal(GVNGCP gvn);

  // Compute the current best Type for this Node, based on the types of its inputs
  abstract public Type value(GVNGCP gvn);

  // Worse-case type for this Node
  public Type all_type() { return Type.ALL; }
  
  // Operator precedence is only valid for ConNode of binary functions
  public int op_prec() { return -1; }

  // Hash is function+inputs, or opcode+input_uids, and is invariant over edge
  // order (so we can swap edges without rehashing)
  @Override public int hashCode() {
    int sum = _op;
    for( int i=0; i<_defs._len; i++ ) if( _defs._es[i] != null ) sum ^= _defs._es[i]._uid;
    return sum;
  }
  // Equals is function+inputs, or opcode+input_uids.  Uses pointer-equality
  // checks for input equality checks.
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof Node) ) return false;
    Node n = (Node)o;
    if( _op != n._op ) return false;
    if( _defs._len != n._defs._len ) return false;
    // Note pointer-equality
    for( int i=0; i<_defs._len; i++ ) if( _defs._es[i] != n._defs._es[i] ) return false;
    return true;
  }

  public void walk( BitSet bs ) {
    assert _defs != null;
    if( !bs.get(_uid) ) {
      assert !is_dead();
      bs.set(_uid);
      for( Node def : _defs )
        if( def != null )
          def.walk(bs);
    }
  }

  public boolean is_dead() { return _uses == null; }
  public void set_dead( ) { _defs = _uses = null; }   // TODO: Poor-mans indication of a dead node, probably needs to recycle these...
}
