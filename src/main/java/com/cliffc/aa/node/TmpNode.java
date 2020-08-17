package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;

import java.lang.AutoCloseable;

// Sea-of-Nodes
public class TmpNode extends Node implements AutoCloseable {
  public TmpNode() { super(OP_TMP); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(byte opt_mode) { return Type.ALL; }
  // TmpNodes are never equal
  @Override public int hashCode() { return 123456789; }
  @Override public boolean equals(Object o) { return this==o; }

  void set_def( int i, Node n ) {
    assert i>= _defs._len || _defs._es[i]==null;
    _defs.setX(i,n);
    if( n != null ) n._uses.add(this);
  }
  
  // Parser support of small lists of nodes to be kept alive during parsing
  public void remove( int i ) {
    Node n = _defs.remove(i);
    n._uses.del(this);
    if( n._uses._len==0 )
      Env.GVN.kill(n); // Recursively begin deleting
  }
  // Parser support of small lists of nodes to be kept alive during parsing.
  // Nuke this node and anything it keeps alive
  @Override public void close() { Env.GVN.kill_new(this); }
}
