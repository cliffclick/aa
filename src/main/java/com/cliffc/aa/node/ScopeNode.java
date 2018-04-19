package com.cliffc.aa.node;

import com.cliffc.aa.*;
import java.util.HashMap;

// Lexical-Scope Node.  
public class ScopeNode extends Node {
  // Mapping from names to def indices
  private final HashMap<String, Integer> _vals;
  
  public ScopeNode() { super(OP_SCOPE); _vals = new HashMap<>(); }

  // Name to node lookup, or null
  public Node get(String name) {
    Integer ii = _vals.get(name);
    return ii==null ? null : _defs.at(ii);
  }
  
  // Add a Node to an UnresolvedNode.  Must be a function.
  public void add_fun(String name, RetNode ret) {
    Integer ii = _vals.get(name);
    Node unr = ii==null ? add(name,new UnresolvedNode()) : _defs.at(ii);
    unr.add_def(ret);
  }
  
  // Extend the current Scope with a new name; cannot override existing name.
  public Node add( String name, Node val ) {
    assert _vals.get(name)==null;
    _vals.put( name, _defs._len );
    add_def(val);
    return val;
  }
  
  // Update the current Scope name
  public Node update( String name, Node val, GVNGCM gvn ) {
    int idx = _vals.get(name); // NPE if name does not exist
    set_def(idx,val,gvn);
    return val;
  }

  /** Return a ScopeNode with all the variable indices at or past the idx.
   *  @param idx index to split on
   *  @return a ScopeNode with the higher indices; 'this' has the lower indices.  null if no new vars
   */
  public ScopeNode split( int idx ) {
    int oldlen = _defs._len;
    if( idx == oldlen ) return null; // No vars, no return
    ScopeNode s = new ScopeNode();
    while( _defs._len > idx )
      for( String name : _vals.keySet() )
        if( _vals.get(name)==_defs._len-1 ) {
          s.add(name,_defs.pop());
          _vals.remove(name);
          break;
        }
    assert _defs._len+s._defs._len==oldlen;
    return s;
  }

  // Add PhiNodes and variable mappings for common definitions
  public void common( Node ctrl, ScopeNode t, ScopeNode f, GVNGCM gvn ) {
    if( t!=null && f!=null ) {  // Might have some variables in common
      for( String name : t._vals.keySet() ) {
        Integer fii =  f._vals.get(name);
        if( fii==null ) continue;
        Node tn = t.at(t._vals.get(name));
        Node fn = f.at(fii);
        add(name,gvn.xform(new PhiNode(ctrl,tn,fn)));
      }
    }
    if( t!=null ) gvn.kill_new(t);
    if( f!=null ) gvn.kill_new(f);
  }
  
  @Override String str() { return "scope"; }
  @Override public String toString() { return "scope"; } // TODO: print with names
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return Type.CONTROL; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  @Override public int hashCode() { return 123456789; }
}
