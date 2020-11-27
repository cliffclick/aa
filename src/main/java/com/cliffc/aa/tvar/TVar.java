package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
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
  final int _uid;

  public TVar( TNode tn ) { this(tn==null ? new TNode[0] : new TNode[]{tn}); }
  public TVar(          ) { this(new TNode[0]); }
  private TVar( TNode[] tns ) { _ns = new Ary<>(tns); _uid = UID++; }

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

  // Structural unification, "this into that".
  // Top-level entry point, not recursive.
  public final TVar unify(TVar tv) {
    if( this==tv ) return this; // Done!
    if( !_will_unify(tv,0, new NonBlockingHashMapLong<>()) ) // Will fail to unify
      //throw unimpl();
      System.out.println("Failed to unify "+this+" and "+tv);
    return _unify0(tv);
  }

  // Recursive entry point for unification.
  final TVar _unify0(TVar tv) {
    if( this==tv ) return this; // Done!
    if( compareTo(tv) > 0 )
      return tv._unify0(this); // Canonicalize unification order
    // Unify this into that
    _u = tv;
    // Kill tnodes and other bits of this, to signify unified.
    if( _ns != null )
      tv._ns  = tv._ns  ==null ? _ns  : Ary.merge_or(_ns  ,tv._ns  , TNode::compareTo);
    if( _deps!=null ) {
      for( TNode tn : _deps )
        tv.push_dep(tn);
      TNode.add_work_all(_deps);
    }
    assert tv.check_ns();
    _deps = _ns = null;
    // Unify parts
    _unify(tv);
    return tv;
  }

  // Unify parts, varies by subclass.
  // Plain TVars have no structure and unify with all others.
  void _unify(TVar tv) { }

  // Sorted, no dups.  Poor-mans assert
  private boolean check_ns() {
    if( _ns!=null )
      for( int i=0; i<_ns._len-1; i++ )
        if( _ns.at(i).uid() >= _ns.at(i+1).uid() )
          return false;
    if( _deps!=null )
      for( int i=0; i<_deps._len-1; i++ )
        if( _deps.at(i).uid() >= _deps.at(i+1).uid() )
          return false;
    return true;
  }

  // Unification requires equal structure; structure varies by subclass.
  // Plain TVars have no structure and unify with all others.
  boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) { return true; }

  // Return a "fresh" copy, preserving structure
  boolean _fresh_unify(TVar tv, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    assert _u==null;                // At top
    if( this==tv ) return false;    // Short cut
    if( occurs_in(nongen, null) ) { // If 'this' is in the non-generative set, use 'this'
      if( !test ) _unify0(tv);      // Unify with LHS always reports progress
      return true;
    } 
    // Use a 'fresh' TVar, but keep the structural properties: if it appears
    // only once, unification with fresh is a no-op.  So instead record as-if
    // unified with fresh.  Only progress if using for the 2nd time.
    TVar prior = dups.get(this);    // Get a replacement, if any
    if( prior==null ) {             // No prior mapping, so...
      dups.put(this,tv);            // Record mapping
      return false;                 // No progress
    }
    if( prior==tv ) return false;
    if( !test ) prior._unify0(tv); // Force structural equivalence
    return true;                // Progress
  }

  // Does 'this' occur in the nongen set, recursively.
  final boolean occurs_in(HashSet<TVar> nongen, VBitSet visit) {
    assert _u==null;            // At top
    if( nongen == null ) return false;
    for( TVar tv : nongen )
      if( tv.find()._occurs_in(this,visit) ) // Flip sense: nongen is now 'this'
        return true;
    return false;
  }
  // Flipped: does 'id' occur in 'this'
  boolean _occurs_in(TVar id, VBitSet visit) {
    assert _u==null && id._u==null; // At top
    return this==id;
  }

  // True if two TVars are structurally equivalent
  static final HashMap<TVar,TVar> EQS = new HashMap<>();
  static final BitSetSparse DUPS = new BitSetSparse();
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
    // Find a sample node to print out
    int idx = _ns.find(e -> !e.is_dead());
    if( idx != -1 ) {
      TNode tn = _ns.at(idx);
      sb.p('N').p(tn.uid()).p(':').p(tn.xstr()).p(':');
    }
    // Print all unioned nodes
    if( debug )
      for( TNode tn : _ns )
        if( (idx==-1 || _ns.at(idx)!=tn) )
          sb.p('N').p(tn.uid()).p(':');
    return _str(sb,bs,debug);
  }
  // Type-variable structure print
  SB _str(SB sb, VBitSet bs, boolean debug) { return sb; } // No special fields

  // Dead is always least; then plain TVars; then any other TVar type.
  // Two equal classes order by uid.
  @Override public int compareTo(TVar tv) {
    if( this==tv ) return 0;
    boolean istv0 =    getClass()==TVar.class;
    boolean istv1 = tv.getClass()==TVar.class;
    if( istv0 && !istv1 ) return -1;
    if( !istv0 && istv1 ) return  1;
    return _uid - tv._uid;
  }

  // Push on deps list.  Returns true if already on the deps lift (no change).
  void push_dep(TNode tn) {
    if( _deps==null ) _deps = new Ary<>(TNode.class);
    if( !tn.is_dead() && _deps.find(tn)==-1 ) {
      _deps.push(tn);
      _deps.sort_update(TNode::compareTo);
    }
  }

}
