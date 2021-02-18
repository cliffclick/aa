package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.HashSet;

// Type Variable.  TVars unify (ala Tarjan Union-Find), and can have structure
// (such as "{ A -> B }").  TVars are tied to a TNode to enforce Type structure
// on Types.  TVars with no structure either refer to a plain Node, or get
// unioned into another TVar.  TVars with structure have to match structure to
// be unified, but then can be recursively unified.

public class TVar implements Comparable<TVar> {
  // Tarjan U-F value.  null==HEAD.
  TVar _u;                      // Tarjan Union-Find; null==HEAD
  // Set of unioned Nodes.  Try for the assert that HEAD has least uid.
  public Ary<TNode> _ns;        // TNodes unioned together.
  // Set of dependent Nodes (to be re-worklisted if something changes)
  public Ary<TNode> _deps;


  static private int UID=1;
  public final int _uid;

  public TVar( TNode tn ) { this(tn==null ? new TNode[0] : new TNode[]{tn}); }
  public TVar(          ) { this(new TNode[0]); }
  private TVar( TNode[] tns ) { _ns = new Ary<>(tns); _uid = UID++; }

  // A TNode resets its TVar.  Remove all instances & start afresh.
  public TVar reset_tnode(TNode tn) { return reset_tnode(tn, new TVar(tn)); }
  public TVar reset_tnode(TNode tn, TVar tv) {
    if( _ns!=null ) {
      int idx = _ns.find(tn);
      if( idx != -1 ) _ns.remove(idx);
    }
    return tv;
  }


  // U-F Find
  public TVar find() {
    if( _u   == null ) return this;
    if( _u._u== null ) return _u;
    TVar u = _u;                // Find top of U-F
    while( u._u != null ) u = u._u;
    TVar v = this;              // Roll up to top of U-F
    while( v != u ) { _u = u; v = v._u; }
    return u;
  }
  // Find without the Union bit
  public TVar debug_find() {
    if( _u   == null ) return this;
    if( _u._u== null ) return _u;
    TVar u = _u;                // Find top of U-F
    while( u._u != null ) u = u._u;
    return u;
  }

  // Structural unification, "this into that".
  // Returns true for progress.
  // Top-level entry point, not recursive.
  public final boolean unify(TVar tv, boolean test) { return _unify0(tv, test); }

  // Recursive entry point for unification.
  boolean _unify0(TVar tv, boolean test) {
    assert _u==null && tv._u==null;
    if( this==tv ) return false; // Done!
    if( compareTo(tv) > 0 )
      return tv._unify0(this,test); // Canonicalize unification order
    if( test ) return true;
    // Unify this into that
    _u = tv;
    if( _ns != null ) {         // Also merge TNodes
      if( tv._ns==null ) tv._ns = _ns;
      else {
        tv._ns = Ary.merge_or(_ns,tv._ns, TNode::compareTo, e->!e.is_dead());
        assert tv.check_ns();   // Check sorted, dead cleared
      }
      TNode.add_flow_uses(tv._ns); // this is picking up structure, children might need to recheck
    }
    if( tv._ns!=null && tv._ns._len==0 ) tv._ns=null;
    if( _deps!=null ) {                         // Also merge deps
      TNode.add_flow(tv.push_deps(_deps,null)); // And push deps on worklist
      assert tv._deps==null || tv._deps.find(TNode::is_dead) == -1;
    }
    if( tv._deps!=null && tv._deps._len==0 )
      tv._deps=null;            // Cleaned out
    // Kill tnodes and other bits of this, to signify unified.
    _deps = _ns = null;
    // Unify parts
    _unify(tv);
    return true;
  }

  // Unify parts, varies by subclass.
  // Plain TVars have no structure and unify with all others.
  void _unify(TVar tv) { }

  // Sorted, no dups.  JOIN of all Nodes is feasible.  Poor-mans assert.
  private boolean check_ns() {
    //Type t = Type.ALL;
    for( int i=0; i<_ns._len-1; i++ ) {
      if( _ns.at(i).uid() >= _ns.at(i+1).uid() || _ns.at(i).is_dead() )
        return false;
      //t = t.join(_ns.at(i).val());
      //if( t.above_center() )
      //  return false;
    }
    return true;
  }

  // Unification requires equal structure; structure varies by subclass.
  // Plain TVars have no structure and unify with all others.
  boolean _will_unify(TVar tv, int cnt) { return true; }

  // Return a "fresh" copy, preserving structure
  boolean _fresh_unify(int cnt, TVar tv, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    assert _u==null;             // At top
    if( this==tv || tv instanceof TVDead ) return false; // Short cut
    if( occurs_in(nongen) )      // If 'this' is in the non-generative set, use 'this'
      return _unify0(tv,test);   // Unify with LHS

    // Use a 'fresh' TVar, but keep the structural properties: if it appears
    // only once, unification with fresh is a no-op.  So instead record as-if
    // unified with fresh.  Only progress if using for the 2nd time.
    TVar prior = dups.get(this);    // Get a replacement, if any
    if( prior==null ) {             // No prior mapping, so...
      dups.put(this,tv);            // Record mapping
      return false;                 // No progress
    }
    TVar prior2 = prior.find();
    if( prior2==tv ) return false;
    return prior2._unify0(tv,test); // Force structural equivalence
  }

  // Does 'this' occur in the nongen set, recursively.
  static final VBitSet VISIT = new VBitSet();
  static       boolean VISIT_BUSY = false;
  final boolean occurs_in(HashSet<TVar> nongen) {
    assert _u==null;            // At top
    if( nongen == null ) return false;
    assert !VISIT_BUSY && VISIT.isEmpty();
    VISIT_BUSY = true;
    boolean occurs=false;
    for( TVar tv : nongen )
      if( tv.find()._occurs_in(this) ) // Flip sense: nongen is now 'this'
        { occurs = true; break; }
    VISIT.clear();
    VISIT_BUSY = false;
    return occurs;
  }
  // Flipped: does 'id' occur in 'this'
  boolean _occurs_in(TVar id) {
    assert _u==null && id._u==null; // At top
    return this==id;
  }

  // Find instances of 'tv' inside of 'this' via structural recursion.  Walk
  // the matching Type at the same time.  Report the first one found, and
  // assert all the others have the same Type.
  static final BitSetSparse DUPS = new BitSetSparse();
  public Type find_tvar(Type t, TVar tv) { DUPS.clear(); return _find_tvar(t,tv,null); }
  Type _find_tvar(Type t, TVar tv, Type t2) { return _find_tvar_self(t,tv,t2); }
  final Type _find_tvar_self(Type t, TVar tv, Type t2) {
    if( tv!=this || t==Type.ANY ) return t2;
    if( t2==null ) return t;
    assert t2==t : "Found multiple refs to tvar with diff types, "+ t +","+ t2;
    //t2 = t2.meet(t);
    return t2;
  }

  // True if two TVars are structurally equivalent
  static final HashMap<TVar,TVar> EQS = new HashMap<>();
  public final boolean eq( TVar tv ) {  EQS.clear();  DUPS.clear();  return _eq(tv);  }
  boolean _eq(TVar tv) {
    assert _u==null && tv._u==null;
    if( this==tv ) return true;
    if( tv.getClass() != TVar.class ) return false;
    // TODO: Something to do with Types
    TVar v2 = EQS.computeIfAbsent(this,k -> tv);
    return tv==v2;              // Unequal TVars
  }


  @Override public final String toString() { return str(new SB(),new VBitSet(),true).toString();  }

  // Pretty print
  public final SB str(SB sb, VBitSet bs, boolean debug) {
    // Explicit U-F chain
    if( _u!=null ) {
      if( debug ) sb.p("V").p(_uid).p(">>");
      return _u.str(sb,bs,debug);
    }
    if( _uid != -1 && bs.tset(_uid) )
      return sb.p("V").p(_uid).p("$");
    // Print all unioned nodes
    if( _ns!=null )             // Have any
      for( TNode tn : _ns )     // For all unioned
        if( !tn.is_dead() ) {   // Dead lazily cleared out, do not both  to print
          sb.p('N').p(tn.uid()).p(':');
          if( !debug ) break;   // Debug, see them all; non-debug just the first
        }
    return _str(sb,bs,debug);   // Subclass specific prints
  }

  // Type-variable structure print
  SB _str(SB sb, VBitSet bs, boolean debug) { return (_ns==null || _ns._len==0) ? sb.p("V").p(_uid) : sb; } // No special fields

  // Dead & Nil are always least; then plain TVars; then any other TVar type.
  // Two equal classes order by uid.
  @Override public int compareTo(TVar tv) {
    if( this==tv ) return 0;
    if( this instanceof TVDead   && !( tv  instanceof TVDead  ) ) return  1; // TVDead   always loses
    if( tv   instanceof TVDead   && !(this instanceof TVDead  ) ) return -1;
    if( this instanceof TVUnused && !( tv  instanceof TVUnused) ) return -1; // TVUnused always wins
    if( tv   instanceof TVUnused && !(this instanceof TVUnused) ) return  1;
    if( this instanceof TNil   ) return -1; // TNil loses second
    if( tv   instanceof TNil   ) return  1;
    boolean istv0 =    getClass()==TVar.class;
    boolean istv1 = tv.getClass()==TVar.class;
    if( istv0 && !istv1 ) return -1; // Plain TVars ahead of others
    if( !istv0 && istv1 ) return  1;
    return tv._uid - _uid;      // Two random subclasses sort by uid
  }

  // Push on deps list.  Returns the merged list.
  public TNode      push_dep (    TNode  tn  , VBitSet visit) { return merge_dep (tn  ); }
         Ary<TNode> push_deps(Ary<TNode> deps, VBitSet visit) { return merge_deps(deps); }
  final TNode merge_dep(TNode tn) {
    if( tn.is_dead() ) return tn;
    if( _deps==null ) _deps = new Ary<>(TNode.class);
    if( _deps.find(tn)==-1 )
      _deps.push(tn);
    return tn;
  }
  // Push on deps list.  Returns the merged list.
  final Ary<TNode> merge_deps(Ary<TNode> deps) {
    if( deps==null ) return _deps;
    deps.filter_update(e->!e.is_dead());
    if( _deps==null ) _deps = deps;
    else {
      _deps.filter_update(e->!e.is_dead());
      for( TNode tn : deps )
        if( _deps.find(tn)==-1 )
          _deps.push(tn);
    }
    if( _deps._len==0 ) _deps=null;
    return _deps;
  }
}
