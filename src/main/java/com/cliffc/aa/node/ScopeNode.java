package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;

import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Predicate;

// Lexical-Scope Node.  
public class ScopeNode extends Node {
  // Mapping from names to def indices.  Named defs are added upfront and some
  // unnamed defs are added & removed as part of parsing.  Named function defs
  // point to ConNodes with a TypeFun constant (a single function), or maybe
  // an Unresolved collection of overloaded functions.
  private final HashMap<String, Integer> _vals;
  private final BitSet _ms;     // True if mutable, indexed with input#
  // Mapping from type-variables to Types.  Types have a scope lifetime like values.
  private final HashMap<String,Type> _types; // user-typing type names
  public ScopeNode() { super(OP_SCOPE); _vals = new HashMap<>(); _types = new HashMap<>(); _ms = new BitSet(); }

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
  public EpilogNode add_fun(String name, EpilogNode epi) {
    Integer ii = _vals.get(name);
    if( ii==null ) {
      update(name,epi,null,false);
    } else {
      Node n = _defs.at(ii);
      if( n instanceof UnresolvedNode ) n.add_def(epi);
      else set_def(ii,new UnresolvedNode(n,epi),null);
    }
    return epi;
  }
  
  // Add or update the scope with a name
  public Node update( String name, Node val, GVNGCM gvn, boolean mutable ) {
    Integer ii = _vals.get(name);
    if( ii==null ) {
      int i=_defs._len;
      _vals.put( name, i );
      add_def(val);
      if( mutable ) _ms.set(i);
    } else {
      int i=ii;
      assert _ms.get(i);
      set_def(i,val,gvn);
      if( !mutable ) _ms.clear(i);
    }
    return val;
  }

  // Set value to null and return it, without deleting node
  public Node remove( String name ) {
    int idx = _vals.get(name); // NPE if name does not exist
    Node n = in(idx);          // Get existing value
    _defs.set(idx,null);       // Set to null, without deleting old
    n._uses.del(n._uses.find(this));
    return n;
  }

  // Name must exist
  public boolean is_mutable( String name ) {
    return _ms.get(_vals.get(name));
  }

  // The current local scope ends; delete local var refs.  Forward refs first
  // found in this scope are assumed to be defined in some outer scope and get
  // promoted.
  public void promote_forward_del_locals(GVNGCM gvn, ScopeNode parent) {
    for( String name : _vals.keySet() ) {
      int idx = _vals.get(name);
      Node n = in(idx);
      if( n != null && parent != null && n.is_forward_ref() )
        parent.update(name,n,null,false);
      if( n != null ) gvn.add_work(n);
      set_def(idx, null, gvn);
      if( is_dead() ) return;
    }
  }
  
  // Add base types on startup
  public void init0() { Type.init0(_types); }
  
  // Name to type lookup, or null
  public Type get_type(String name) { return _types.get(name);  }
  public HashMap<String,Type> types() { return _types; }
  
  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, Type t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
  }
  
  /** Return a ScopeNode with all the variable indices at or past the idx;
   *  remove them from 'this' ScopeNode.
   *  @param idx index to split on
   *  @param tmp A list of dull nodes, used to reverse sharpening after the if arm closes
   *  @return a ScopeNode with the higher indices; 'this' has the lower indices.  null if no new vars
   */
  public ScopeNode split( int idx, TmpNode tmp, GVNGCM gvn ) {
    // Recover old 'dull' values after a sharpening if-test ends.
    for( int i=0; i<tmp._defs._len; i++ ) {
      if( tmp.in(i) != null ) {
        assert in(i) != tmp.in(i) && in(i) != null;
        set_def(i,tmp.in(i),gvn);
      }
    }
    
    int oldlen = _defs._len;
    if( idx == oldlen ) return null; // No vars, no return
    ScopeNode s = new ScopeNode();
    while( _defs._len > idx ) {
      int lidx = _defs._len-1;
      for( String name : _vals.keySet() )
        if( _vals.get(name)==lidx ) {
          s.update(name,pop(),null,_ms.get(lidx));
          _vals.remove(name);
          _ms.clear(lidx);
          break;
        }
    }
    assert _defs._len+s._defs._len==oldlen;
    return s;
  }

  // Add PhiNodes and variable mappings for common definitions merging at the
  // end of an IfNode split.
  // - Errors are ignored for dead vars (ErrNode inserted into graph as instead
  //   of a syntax error)
  // - Unknown forward refs must be unknown on both branches and be immutable
  //   and will promote to the next outer scope.
  // - First-time defs on either branch must be defined on both branches.
  // - Both branches must agree on mutability
  // - Ok to be mutably updated on only one arm
  public void common( Parse P, GVNGCM gvn, String phi_errmsg, ScopeNode t, ScopeNode f ) {
    if( t!=null )               // Might have some variables in common
      for( String name : t._vals.keySet() )
        if( f==null || f._vals.get(name) == null )// If not on false side
          do_one_side(name,P,gvn,phi_errmsg,t,true);
        else
          do_both_sides(name,P,gvn,phi_errmsg,t,f);

    if( f!=null )               // Might have some variables in common
      for( String name : f._vals.keySet() )
        if( t==null || t._vals.get(name) == null )// If not on true side
          do_one_side(name,P,gvn,phi_errmsg,f,false);
    
    if( t!=null ) Env._gvn.kill_new(t);
    if( f!=null ) Env._gvn.kill_new(f);
  }


  // Called per name defined on only one arm of a trinary.
  // Produces the merge result.
  private void do_one_side(String name, Parse P, GVNGCM gvn, String phi_errmsg, ScopeNode x, boolean arm) {
    int xii = x._vals.get(name);
    boolean x_is_mutable = x._ms.get(xii);
    Node xn = x.in(xii);

    // Forward refs are not really a def, but produce a trackable definition
    // that must be immutable, and will eventually get promoted until it
    // reaches a scope where it gets defined.
    if( xn.is_forward_ref() ) { assert !x_is_mutable; update(name,xn,gvn,false); return; }
        
    // Check for mixed-mode updates.  'name' must be either fully mutable or
    // fully immutable at the merge point (or dead afterwards).  Since x was
    // updated on this branch, the variable was mutable beforehand.  Since it
    // was mutable and not changed on the other side, it remains mutable.
    if( !x_is_mutable ) {       // x-side is final but y-side is mutable.
      update(name,P.err_ctrl1(" is only partially mutable",gvn.type(xn).widen()),gvn,false);
      return;
    }

    // Must be mutable.  Find the prior definition.
    Node yn = P.lookup(name);
    if( yn == null ) {
      update(name,P.err_ctrl1("'"+name+"' not defined on "+!arm+" arm of trinary",gvn.type(xn).widen()),gvn,false);
      return;
    } 
    // Mutably updated on one side, and remains mutable.
    update(name,xn==yn ? xn : P.gvn(new PhiNode(phi_errmsg, P.ctrl(),xn,yn)),gvn,true);
  }
  
  private void do_both_sides(String name, Parse P, GVNGCM gvn, String phi_errmsg, ScopeNode t, ScopeNode f) {
    int tii = t._vals.get(name);
    int fii = f._vals.get(name);
    boolean t_is_mutable = t._ms.get(tii);
    boolean f_is_mutable = f._ms.get(fii);
    Node tn = t.in(tii);
    Node fn = f.in(fii);
    
    if( tn.is_forward_ref() ) {
      assert !t_is_mutable;
      if( fn.is_forward_ref() ) {
        assert !f_is_mutable;
        throw AA.unimpl(); // Merge/U-F two forward refs
      }
      update(name,P.err_ctrl1("'"+name+"' not defined on "+true+" arm of trinary",gvn.type(fn).widen()),gvn,false);
      return;
    }
    if( fn.is_forward_ref() ) {
      update(name,P.err_ctrl1("'"+name+"' not defined on "+false+" arm of trinary",gvn.type(tn).widen()),gvn,false);
      return;
    }

    // Check for mixed-mode updates.  'name' must be either fully mutable
    // or fully immutable at the merge point (or dead afterwards).
    if( t_is_mutable != f_is_mutable ) {
      update(name,P.err_ctrl1(" is only partially mutable",gvn.type(tn).widen()),gvn,false);
      return;
    }

    update(name,tn==fn ? fn : P.gvn(new PhiNode(phi_errmsg, P.ctrl(),tn,fn)),gvn,t_is_mutable);
  }
  
  private Node undef(Parse P, GVNGCM gvn, Node xn, String name, boolean arm ) {
    return xn.is_forward_ref() ? xn :
      P.err_ctrl1("'"+name+"' not defined on "+arm+" arm of trinary",gvn.type(xn).widen());
  }
  private void add_phi(Parse P, String errmsg, String name, Node tn, Node fn, boolean mutable) {
    update(name,tn==fn ? fn : P.gvn(new PhiNode(errmsg, P.ctrl(),tn,fn)),null,mutable);
  }

  // Replace uses of dull with sharp, used after an IfNode test
  void sharpen( Node dull, Node sharp, TmpNode tmp ) {
    for( int i=0; i<_defs._len; i++ )
      if( in(i)==dull ) {
        tmp.set_def(i,dull);    // Save dull for recovery after If arm passes
        set_def(i,sharp,null);  // ok for gvn to be passed null, because 'dull' never deleted
      }
  }
  
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return all_type(); }
  @Override public Type all_type() { return Type.CTRL; }
  @Override public int hashCode() { return 123456789; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  // End of dominator tree; do not walk past
  @Override Node walk_dom_last(Predicate<Node> P) { return P.test(this) ? this : null; }
}
