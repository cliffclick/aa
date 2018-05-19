package com.cliffc.aa.node;

import com.cliffc.aa.*;

import java.lang.AutoCloseable;

// Sea-of-Nodes
public class TmpNode extends Node implements AutoCloseable {
  public TmpNode() { super(OP_TMP); }
  @Override String str() { return "tmp"; }
  @Override public String toString() { return "tmp"; } // TOoOoOo many use/defs, print none
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return TypeErr.ALL; }
  // TmpNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  @Override public int hashCode() { return 123456789; }

  void set_def( int i, Node n ) {
    assert i>= _defs._len || _defs._es[i]==null;
    _defs.setX(i,n);
    if( n != null ) n._uses.add(this);
  }
  
  // Parser support of small lists of nodes to be kept alive during parsing
  public void remove( int i ) {
    Node n = _defs.remove(i);
    n._uses.del(n._uses.find(a -> a==this));
    if( n._uses._len==0 )
      Env._gvn.kill(n); // Recursively begin deleting
  }
  // Parser support of small lists of nodes to be kept alive during parsing.
  // Nuke this node and anything it keeps alive
  @Override public void close() { Env._gvn.kill_new(this); }
}
