package com.cliffc.aa.node;

import com.cliffc.aa.*;
import java.util.HashMap;

// Lexical-Scope Node.  
public class ScopeNode extends Node {
  // Mapping from names to def indices
  private final HashMap<String, Integer> _vals;
  
  public ScopeNode() { super(OP_SCOPE); }

  // Name to node lookup, or null
  Node get(String name) {
    Integer ii = _vals.get(name);
    return ii==null ? null : _defs.at(ii);
  }
  
  // Add a Node to an UnresolvedNode
  void add_fun(String name, Node ret) {
    Integer ii = _vals.get(name);
    Node unr = ii==null ? add(name,new UnresolvedNode()) : _defs.at(ii);
    unr.add_def(ret);
  }
  
  // Extend the current Scope with a new name.
  Node add( String name, Node val ) {
    assert _vals.get(name)==null;
    _root.add_def(val);
    _vals.put( name, _root._len );
    return val;
  }

  @Override String str() { return "scope"; }
  @Override public String toString() { return "scope"; } // TODO: print with names
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return Type.ALL; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  @Override public int hashCode() { return 123456789; }
}
