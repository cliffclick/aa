package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeErr;
import java.util.HashMap;

// Lexical-Scope Node.  
public class ScopeNode extends Node {
  // Mapping from names to def indices.  Named defs are added upfront and some
  // unnamed defs are added & removed as part of parsing.  Named function defs
  // point to ConNodes with a TypeFun constant (a single function) or a
  // TypeUnion of TypeFuns.
  private final HashMap<String, Integer> _vals;
  // Mapping from type-variables to Types.  Types have a scope lifetime like values.
  private final HashMap<String,Type> _types; // user-typing type names
  public ScopeNode() { super(OP_SCOPE); _vals = new HashMap<>(); _types = new HashMap<>(); }

  // Name to node lookup, or null
  public Node get(String name) {
    Integer ii = _vals.get(name);
    return ii==null ? null : _defs.at(ii);
  }
  // Get a set of names into an array.  Skip zero, which is control.
  public Node[] get( Ary<String> names ) {
    Node[] ns = new Node[names._len+1];
    for( int i=0; i<names._len; i++ )
      ns[i+1] = get(names.at(i));
    return ns;
  }
  
  // Add a Node to an UnresolvedNode.  Must be a function.
  public void add_fun(String name, EpilogNode epi) {
    Integer ii = _vals.get(name);
    if( ii==null ) add(name,epi);
    else {
      Node n = _defs.at(ii);
      if( n instanceof UnresolvedNode ) n.add_def(epi);
      else set_def(ii,new UnresolvedNode(n,epi),null);
    }
  }
  
  // Extend the current Scope with a new name; cannot override existing name.
  public Node add( String name, Node val ) {
    assert _vals.get(name)==null;
    _vals.put( name, _defs._len );
    add_def(val);
    return val;
  }
  
  // Update the current Scope name
  public void update( String name, Node val, GVNGCM gvn ) {
    int idx = _vals.get(name); // NPE if name does not exist
    set_def(idx,val,gvn);
  }

  // The current local scope ends; delete local var refs.  Forward refs first
  // found in this scope are assumed to be defined in some outer scope and get
  // promoted.
  public void promote_forward_del_locals(GVNGCM gvn, ScopeNode parent) {
    for( String name : _vals.keySet() ) {
      int idx = _vals.get(name);
      Node n = at(idx);
      if( parent != null && n.is_forward_ref() )
        parent.add(name,n);
      if( n != null ) gvn.add_work(n);
      set_def(idx, null, gvn);
      if( is_dead() ) return;
    }
  }
  
  // Add base types on startup
  public void init0() { Type.init0(_types); }
  
  // Name to type lookup, or null
  public Type get_type(String name) { return _types.get(name);  }
  
  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, Type t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
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
          s.add(name,pop());
          _vals.remove(name);
          break;
        }
    assert _defs._len+s._defs._len==oldlen;
    return s;
  }

  // Add PhiNodes and variable mappings for common definitions
  public void common( Parse P, String errmsg, ScopeNode t, ScopeNode f ) {
    if( t!=null ) {  // Might have some variables in common
      for( String name : t._vals.keySet() ) {
        Node tn = t.at(t._vals.get(name));
        Integer fii = f==null ? null : f._vals.get(name);
        Node fn = fii==null ? undef(P,tn,name,false) : f.at(fii); // Grab false-side var
        add_phi(P,errmsg,name,tn,fn);
      }
    }
    if( f!=null ) {  // Might have some variables in common
      for( String name : f._vals.keySet() ) {
        Node fn = f.at(f._vals.get(name));
        Integer tii = t==null ? null : t._vals.get(name);
        if( tii == null ) {     // Only defined on one branch
          Node tn = undef(P,fn,name,true); // True-side var
          add_phi(P,errmsg,name,tn,fn);
        } // Else values defined on both branches already handled
      }
    }
    if( t!=null ) Env._gvn.kill_new(t);
    if( f!=null ) Env._gvn.kill_new(f);
  }

  private Node undef(Parse P, Node xn, String name, boolean arm ) {
    return xn.is_forward_ref() ? xn
      : Env._gvn.con(TypeErr.make(P.errMsg("'"+name+"' not defined on "+arm+" arm of trinary")));
  }
  private void add_phi(Parse P, String errmsg, String name, Node tn, Node fn) {
    add(name,tn==fn ? fn : P.gvn(new PhiNode(errmsg, P.ctrl(),tn,fn)));
  }
  
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return Type.CTRL; }
  @Override public Type all_type() { return Type.CTRL; }
  @Override public int hashCode() { return 123456789; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
}
