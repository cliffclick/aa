package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.*;
import java.util.HashMap;

// Type Variable.  TVars unify (ala Tarjan Union-Find), and can have structure
// (such as "{ A -> B }").  TVars are tied to a TNode to enforce Type structure
// on Types.  TVars with no structure either refer to a plain Node, or get
// unioned into another TVar.  TVars with structure have to match structure to
// be unified, but then can be recursively unified.

public class TVar implements Comparable<TVar> {
  // Tarjan U-F value.  null==HEAD.
  TVar _u;                      // Tarjan Union-Find; null==HEAD
  // Set of unioned Nodes.  The first element is the HEAD, the original TNode.
  // Dead TNodes are removed as found.  Try for the assert that HEAD has least uid.
  Ary<TNode> _ns;               // TNodes unioned together.
  int _uid;                     // UID of HEAD TNode; only used for debug prints

  public TVar( TNode tn ) { _ns = new Ary<>(new TNode[]{tn}); _uid = tn.uid(); }

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
    if( _ns != null ) tv._ns = Ary.merge_or(_ns,tv._ns);
    for( int i=0; i<tv._ns._len; i++ )
      if( tv._ns.at(i).is_dead() )
        tv._ns.remove(i--);
    assert tv.check_ns();
    _ns = null;
    // Unify parts
    _unify(tv);
    return tv;
  }

  // Unify parts, varies by subclass.
  // Plain TVars have no structure and unify with all others.
  void _unify(TVar tv) { }

  // Sorted, no dups.  Poor-mans assert
  private boolean check_ns() {
    for( int i=0; i<_ns._len-1; i++ )
      if( _ns.at(i).uid() >= _ns.at(i+1).uid() )
        return false;
    return true;
  }

  // Unification requires equal structure; structure varies by subclass.
  // Plain TVars have no structure and unify with all others.
  boolean _will_unify(TVar tv, int cnt, NonBlockingHashMapLong<Integer> cyc) { return true; }

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
    if( bs.tset(_uid) )
      return sb.p("V").p(_uid).p("$");
    // Find a sample node to print out
    int idx = _ns.find(e -> e.uid()==_uid);
    if( idx == -1 ) idx = _ns.find(e -> !e.is_dead());
    if( idx != -1 ) {
      TNode tn = _ns.at(idx);
      sb.p('N').p(tn.uid()).p(':').p(tn.xstr()).p(':');
    }
    // Print all unioned nodes
    if( debug )
      for( TNode tn : _ns )
        if( !tn.is_dead() && (idx==-1 || _ns.at(idx)!=tn) )
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

}
