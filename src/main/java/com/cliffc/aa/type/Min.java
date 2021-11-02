package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;

import java.util.HashMap;

// Algorithm for minimizing a not-yet-interned graph of Types
public abstract class Min {

  // Install a cyclic structure.  'head' is not interned and points to a
  // (possibly cyclic) graph of not-interned Types.  Minimize the graph, set
  // the hashes everywhere, check for a prior existing Type.  Return a prior,
  // or else set all the duals and intern the entire graph.
  @SuppressWarnings("unchecked")
  public static <T extends Type> T install(T head) {
    Type.RECURSIVE_MEET++;
    _reachable(head);           // Compute 1st-cut reachable
    head = _shrink(head);
    _reachable(head);           // Recompute reachable; probably shrinks
    assert check_uf();
    UF.clear();
    Type.RECURSIVE_MEET--;

    // Set cyclic bits for faster equals/meets.
    assert CSTACK.isEmpty() && CVISIT.cardinality()==0;
    _set_cyclic(head);
    assert CSTACK.isEmpty();   CVISIT.clear();

    // Check for dups.  If found, delete entire cycle, and return original.
    T old = (T)head.intern_lookup();
    if( old != null ) {         // Found prior interned cycle
      for( Type t : REACHABLE ) t.free(null); // Free entire new cycle
      return old;               // Return original cycle
    }
    // Complete cyclic dual
    for( Type t : REACHABLE )
      assert t.intern_lookup()==null && t._dual==null;
    head.rdual();
    // Insert all members of the cycle into the hashcons.  If self-symmetric,
    // also replace entire cycle with self at each point.
    for( Type t : REACHABLE )
      if( t.retern() != t._dual ) t._dual.retern();
    // Return new interned cycle
    return head;
  }


  // -----------------------------------------------------------------
  // Set the cyclic bit on structs in cycles.  Can be handed an arbitrary
  // graph, including a DAG of unrelated Strongly Connected Components.

  // Almost classic cycle-finding algorithm but since Structs have labeled
  // out-edges (with field names), we can have multiple output edges from the
  // same node (struct) to the same TypeMemPtr.  The classic cycle-finders do
  // not work with multi-edges.
  private static final Ary<Type> CSTACK = new Ary<>(Type.class);
  private static final VBitSet CVISIT = new VBitSet();
  private static void _set_cyclic(Type t ) {
    assert t._hash==t.compute_hash(); // Hashes already set by shrink
    if( t.interned() ) return;  // Already interned (so hashed, cyclic set, etc)
    if( CVISIT.test(t._uid) ) { // If visiting again... have found a cycle t->....->t
      // All on the stack are flagged as being part of a cycle
      int i;
      i=CSTACK._len-1;
      while( i >= 0 && CSTACK.at(i)!=t ) i--;
      if( i== -1 ) return;  // Due to multi-edges, we might not find if dupped, so just ignore
      for( ; i < CSTACK._len; i++ ) { // Set cyclic bit
        Type t2 = CSTACK.at(i);
        if( t2 instanceof TypeStruct ) ((TypeStruct)t2)._cyclic = true;
      }
      return;
    }
    CSTACK.push(t);              // Push on stack, in case a cycle is found
    switch( t._type ) {
      case Type.TMEMPTR ->   _set_cyclic(((TypeMemPtr) t)._obj);
      case Type.TFUNPTR -> { _set_cyclic(((TypeFunPtr) t)._dsp); _set_cyclic(((TypeFunPtr) t)._ret); }
      case Type.TFLD    ->   _set_cyclic(((TypeFld) t)._t);
      case Type.TSTRUCT -> {
        CVISIT.set(t._uid);
        for( TypeFld fld : ((TypeStruct) t).flds() ) _set_cyclic(fld);
      }
      default -> throw AA.unimpl();
    }
    CSTACK.pop();               // Pop, not part of anothers cycle
  }

  // -----------------------------------------------------------------
  // Support Disjoint-Set Union-Find on Types
  static final NonBlockingHashMapLong<Type> UF = new NonBlockingHashMapLong<>();
  @SuppressWarnings("unchecked")
  static <T extends Type> T ufind(T t) {
    T t0 = (T)UF.get(t._uid), tu;
    if( t0 == null ) return t;  // One step, hit end of line
    // Find end of U-F line
    while( (tu = (T)UF.get(t0._uid)) != null ) t0=tu;
    // Set whole line to 1-step end of line
    while( (tu = (T)UF.get(t ._uid)) != null ) { assert t._uid != t0._uid; UF.put(t._uid,t0); t=tu; }
    return t0;
  }
  static <T extends Type> T union( T lost, T kept) {
    if( lost == kept ) return kept;
    assert !lost.interned();
    assert UF.get(lost._uid)==null && UF.get(kept._uid)==null;
    assert lost._uid != kept._uid;
    UF.put(lost._uid,kept);
    return kept;
  }

  // Walk, looking for not-minimal.  Happens during 'approx' which might
  // require running several rounds of 'shrink' to fold everything up.
  static boolean check_uf() {
    int err=0;
    HashMap<Type,Type> ss = new HashMap<>();
    for( Type t : REACHABLE ) {
      Type tt;
      if( ss.get(t) != null || // Found unresolved dup; ts0.equals(ts1) but ts0!=ts1
          ((tt = t.intern_lookup()) != null && tt != t) ||
          ufind(t) != t )
        err++;
      ss.put(t,t);
    }
    return err == 0;
  }

  // Reachable collection of Types that form cycles: TypeMemPtr, TypeFunPtr,
  // TypeFld, TypeStruct, and anything not interned reachable from them.
  private static final Ary<Type> REACHABLE = new Ary<>(new Type[1],0);
  private static final BitSetSparse ON_REACH = new BitSetSparse();
  private static void _reachable(Type head) {
    REACHABLE.clear();
    ON_REACH.clear();
    _push(head);
    int idx=0;
    while( idx < REACHABLE._len ) {
      Type t = REACHABLE.at(idx++);
      switch( t._type ) {
      case Type.TMEMPTR:  _push(((TypeMemPtr)t)._obj); break;
      case Type.TFUNPTR:  _push(((TypeFunPtr)t)._dsp); _push(((TypeFunPtr)t)._ret); break;
      case Type.TFLD   :  _push(((TypeFld   )t)._t  ); break;
      case Type.TSTRUCT:  for( TypeFld tf : ((TypeStruct)t).flds() ) _push(tf); break;
      default: break;
      }
    }
  }
  private static void _push( Type t ) {
    if( !t.interned() && !ON_REACH.tset(t._uid) )
      REACHABLE.push(t);
  }

  // This is a Type minimization algorithm done "bottom up" or pessimistically.
  // It repeatedly finds instances of local duplication and removes them,
  // repeating until hitting a fixed point.  Local dups include any already
  // interned Types, or DUPS (local interning or hash-equivalence) or a UF hit.
  // Computes the final hash code as part of intern checking.
  private static final IHashMap DUPS = new IHashMap();
  private static <T extends Type> T _shrink(T nt) {
    assert DUPS.isEmpty();
    // Set all hashes.  Hash recursion stops at TypeStructs, so do them first,
    // then do dependent hashes.
    for( Type t : REACHABLE ) if( t instanceof TypeStruct ) t.set_hash();
    for( Type t : REACHABLE ) if( t instanceof TypeMemPtr ) t.set_hash();
    for( Type t : REACHABLE ) if( t instanceof TypeFunPtr ) t.set_hash();
    for( Type t : REACHABLE ) t.set_hash();    // And all the rest.

    // Need back-edges to do this iteratively in 1 pass.  This algo just sweeps
    // until no more progress, but with generic looping instead of recursion.
    boolean progress = true;
    while( progress ) {
      progress = false;
      DUPS.clear();
      for( Type t : REACHABLE ) {
        Type t0 = ufind(t);
        Type t1 = t0.intern_lookup();
        if( t1==null ) t1 = DUPS.get(t0);
        if( t1 != null ) t1 = ufind(t1);
        if( t1 == t0 ) continue; // This one is already interned
        if( t1 != null ) { union(t0,t1); progress = true; continue; }

        switch( t._type ) {
        case Type.TMEMPTR:      // Update TypeMemPtr internal field
          TypeMemPtr tm = (TypeMemPtr)t0;
          TypeObj t4 = tm._obj;
          TypeObj t5 = ufind(t4);
          if( t4 != t5 ) {
            tm._obj = t5;
            progress |= post_mod(tm);
            if( !t5.interned() ) REACHABLE.push(t5);
          }
          break;
        case Type.TFUNPTR:      // Update TypeFunPtr internal field
          boolean fprogress=false;
          TypeFunPtr tfptr = (TypeFunPtr)t0;
          Type t6 = tfptr._dsp;
          Type t7 = ufind(t6);
          if( t6 != t7 ) {
            tfptr._dsp = t7;
            fprogress = true;
            if( !t7.interned() ) REACHABLE.push(t7);
          }
          t6 = tfptr._ret;
          t7 = ufind(t6);
          if( t6 != t7 ) {
            tfptr._ret = t7;
            fprogress = true;
            if( !t7.interned() ) REACHABLE.push(t7);
          }
          if( fprogress ) progress |= post_mod(tfptr);
          break;
        case Type.TSTRUCT:      // Update all TypeStruct fields
          TypeStruct ts = (TypeStruct)t0;
          for( TypeFld tfld : ts.flds() ) {
            TypeFld tfld2 = ufind(tfld);
            if( tfld != tfld2 ) {
              progress = true;
              ts.set_fld(tfld2);
            }
          }
          break;
        case Type.TFLD:         // Update all TFlds
          TypeFld tfld = (TypeFld)t0;
          Type tft = tfld._t, t2 = ufind(tft);
          if( tft != t2 ) {
            progress = true;
            int old_hash = tfld._hash;
            tfld._t = t2;
            assert old_hash == tfld.compute_hash();
          }
          break;

        default: break;
        }
        DUPS.put(t0);
      }
    }
    DUPS.clear();
    return ufind(nt);
  }

  // Set hash after field mod, and re-install in dups
  private static boolean post_mod(Type t) {
    t._hash = t.compute_hash();
    DUPS.put(t);
    return true;
  }
}
