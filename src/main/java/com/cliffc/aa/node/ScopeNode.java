package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;

import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Predicate;

// Lexical-Scope Node.  Tracks control & phat memory, plus a stack frame (which
// is just a NewNode).  The stack frame maps local variable names to Nodes and
// is modeled as a true memory indirection - for true closures.  Unless there
// is an upwards funarg the stack frame will optimize away.
public class ScopeNode extends Node {

  // Mapping from type-variables to Types.  Types have a scope lifetime like values.
  private final HashMap<String,Type> _types; // user-typing type names

  public ScopeNode(boolean early) {
    super(OP_SCOPE,null,null,null);
    if( early ) { add_def(null); add_def(null); add_def(null); }
    _types = new HashMap<>();
    keep();
  }

  // Add base types on startup
  public void init0() { Type.init0(_types); }

  public    Node ctrl() { return in(0); }
  public    Node mem () { return in(1); }
  public NewNode stk () { return (NewNode)in(2); }
  public void set_ctrl(   Node n, GVNGCM gvn) { set_def(0,n,gvn); }
  public void set_mem (   Node n, GVNGCM gvn) { set_def(1,n,gvn); }
  public void set_stk (NewNode n, GVNGCM gvn) { set_def(2,n,gvn); }

  public Node get(String name) { return stk().get(name); }
  public boolean exists(String name) { return get(name)!=null; }
  public boolean is_mutable(String name) { return stk().is_mutable(name); }

  public RegionNode early_ctrl() { return (RegionNode)in(3); }
  public    PhiNode early_mem () { return (   PhiNode)in(4); }
  public    PhiNode early_val () { return (   PhiNode)in(5); }

  // Add a Node to an UnresolvedNode.
  public FunPtrNode add_fun( String name, FunPtrNode ptr) { return stk().add_fun(name,ptr); }

  // Name to type lookup, or null
  public Type get_type(String name) { return _types.get(name);  }
  public HashMap<String,Type> types() { return _types; }

  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, Type t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
  }

  ///** Return a ScopeNode with all the variable indices at or past the idx;
  // *  remove them from 'this' ScopeNode.
  // *  @param idx index to split on
  // *  @param tmp A list of dull nodes, used to reverse sharpening after the if arm closes
  // *  @return a ScopeNode with the higher indices; 'this' has the lower indices.  null if no new vars
  // */
  //public ScopeNode split( int idx, TmpNode tmp, GVNGCM gvn ) {
  //  // Recover old 'dull' values after a sharpening if-test ends.
  //  for( int i=0; i<tmp._defs._len; i++ ) {
  //    if( tmp.in(i) != null ) {
  //      assert in(i) != tmp.in(i) && in(i) != null;
  //      set_def(i,tmp.in(i),gvn);
  //    }
  //  }
  //
  //  int oldlen = _defs._len;
  //  if( idx == oldlen ) return null; // No vars, no return
  //  ScopeNode s = new ScopeNode();
  //  while( _defs._len > idx ) {
  //    int lidx = _defs._len-1;
  //    for( String name : _vals.keySet() )
  //      if( _vals.get(name)==lidx ) {
  //        s.update(name,pop(),null,_ms.get(lidx));
  //        _vals.remove(name);
  //        _ms.clear(lidx);
  //        break;
  //      }
  //  }
  //  assert _defs._len+s._defs._len==oldlen;
  //  return s;
  //}
  
  public void common( Parse P, GVNGCM gvn, String phi_errmsg, ScopeNode t, ScopeNode f, Node dull, Node t_sharp, Node f_sharp ) {
    stk().common(P,gvn,phi_errmsg,t.stk(),f.stk(),dull,t_sharp,f_sharp);
    set_mem(gvn.xform(new PhiNode(null,P.ctrl(),t.mem(),f.mem())),gvn);
  }

  // Wire up an early-function-exit path
  public Node early_exit( Parse P, Node val ) {
    assert early();
    if( early_ctrl() == null ) {
      String phi_errmsg = P.phi_errmsg();
      set_def(3,new RegionNode        ((Node)null),P._gvn);
      set_def(4,new PhiNode(phi_errmsg,(Node)null),P._gvn);
      set_def(5,new PhiNode(phi_errmsg,(Node)null),P._gvn);
    }
    return P.do_exit(early_ctrl(),early_mem(),early_val(),val);
  }
  public boolean early() { return _defs._len==6; }

  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return all_type(); }
  @Override public Type all_type() { return Type.ALL; }
  @Override public int hashCode() { return 123456789; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  // End of dominator tree; do not walk past
  @Override Node walk_dom_last(Predicate<Node> P) { return P.test(this) ? this : null; }
}
