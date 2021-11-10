package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;

import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.IntSupplier;
import java.util.function.UnaryOperator;

import static com.cliffc.aa.AA.unimpl;


// Algorithm for minimizing a not-yet-interned graph of Types
interface Cyclic {

  // Type is cyclic
  boolean cyclic();
  void set_cyclic();

  // Walk and apply a map.  No return, so just for side-effects.
  // Does not recurse.  Does not guard against cycles.
  // TODO: Useful to make a reducing version for side-effect-free summary over a type?
  void walk1( BiFunction<Type,String,Type> map );

  // Map and replace all child_types.  Does not recurse.  Does not guard
  // against cycles.  Example:
  //          [fidx]{    dsp ->     ret   }
  //          cyclic.walk_update( child_type ->  map(child_type) );
  //          [fidx]{map(dsp) -> map(ret) }
  void walk_update( UnaryOperator<Type> map );

  // Install a cyclic structure.  'head' is not interned and points to a
  // (possibly cyclic) graph of not-interned Types.  Minimize the graph, set
  // the hashes everywhere, check for a prior existing Type.  Return a prior,
  // or else set all the duals and intern the entire graph.
  @SuppressWarnings("unchecked")
  static <T extends Type> T install( T head ) {
    Type.RECURSIVE_MEET++;
    _reachable(head,true);      // Compute 1st-cut reachable
    head = _dfa_min(head);
    _reachable(head,false);     // Recompute reachable; skip interned; probably shrinks
    Type.RECURSIVE_MEET--;

    // Set cyclic bits for faster equals/meets.
    assert CSTACK.isEmpty() && CVISIT.cardinality()==0;
    _set_cyclic(head);
    assert CSTACK.isEmpty();   CVISIT.clear();

    // Check for dups.
    T old = (T)head.intern_lookup();
    if( old != null ) return old; // Found prior interned cycle

    // Complete cyclic dual
    head.rdual();
    // Insert all members of the cycle into the hashcons.  If self-symmetric,
    // also replace entire cycle with self at each point.
    for( Type t : REACHABLE )
      if( !t.interned() )
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
  Ary<Type> CSTACK = new Ary<>(Type.class);
  VBitSet CVISIT = new VBitSet();
  static void _set_cyclic(Type t ) {
    assert t._hash==t.compute_hash(); // Hashes already set by shrink
    if( t.interned() ) return;  // Already interned (so hashed, cyclic set, etc)
    if( CVISIT.test(t._uid) ) { // If visiting again... have found a cycle t->....->t
      // All on the stack are flagged as being part of a cycle
      int i=CSTACK._len-1;
      while( i >= 0 && CSTACK.at(i)!=t ) i--;
      if( i== -1 ) return;  // Due to multi-edges, we might not find if dupped, so just ignore
      for( ; i < CSTACK._len; i++ ) { // Set cyclic bit
        Type t2 = CSTACK.at(i);
        if( t2 instanceof Cyclic ) ((Cyclic)t2).set_cyclic();
      }
      return;
    }
    CSTACK.push(t);              // Push on stack, in case a cycle is found
    switch( t._type ) {
    case Type.TMEMPTR ->   _set_cyclic(((TypeMemPtr) t)._obj);
    case Type.TFUNPTR -> { _set_cyclic(((TypeFunPtr) t)._dsp); _set_cyclic(((TypeFunPtr) t)._ret); }
    case Type.TFLD    ->   _set_cyclic(((TypeFld   ) t)._t  );
    case Type.TSTRUCT -> { CVISIT.set(t._uid);  for( TypeFld fld : ((TypeStruct) t).flds() ) _set_cyclic(fld);  }
    default -> throw AA.unimpl();
    }
    CSTACK.pop();               // Pop, not part of another's cycle
  }

  // -----------------------------------------------------------------
  // Reachable collection of Types that form cycles: TypeMemPtr, TypeFunPtr,
  // TypeFld, TypeStruct, and anything not interned reachable from them.
  Ary<Type> REACHABLE = new Ary<>(new Type[1],0);
  BitSetSparse ON_REACH = new BitSetSparse();
  private static void _reachable(Type head, final boolean also_interned) {
    // Efficient 1-pass linear-time algo: the REACHABLE set keeps growing, and
    // idx points to the next not-scanned-but-reached Type.
    REACHABLE.clear();
    ON_REACH.clear();
    REACHABLE.push(head);
    ON_REACH.tset(head._uid);
    for( int idx=0; idx < REACHABLE._len; idx++ ) {
      Type t = REACHABLE.at(idx);
      if( !t.interned() ||      // If not interned, include all children, interned or not
          // Or all of an interned cycle
          (also_interned && t instanceof Cyclic && ((Cyclic)t).cyclic()) )
        ((Cyclic)t).walk1((tc,label) -> !ON_REACH.tset(tc._uid) ? REACHABLE.push(tc) : tc);
    }
  }

  // --------------------------------------------------------------------------
  // This is a Type minimization algorithm done "top down" or optimistically.
  // It is loosely based on Hopcroft DFA minimization or Click thesis.  Edges
  // are labeled via Strings (struct labels) instead of being a small count so
  // the inner loops are reordered to take advantage.

  // Type Partitions based on Click thesis: groups of equivalent Types, that
  // have equal static properties, and equivalent Type edges.
  class Partition implements IntSupplier {
    // Static NBMHL from Type.uid to Partitions
    static final NonBlockingHashMapLong<Partition> TYPE2PART = new NonBlockingHashMapLong<>();
    // All initial Partitions, in an iterable
    static final Ary<Partition> PARTS = new Ary<>(Partition.class);

    static Partition malloc() {
      Partition P = PARTS.inc_len();
      if( P==null ) PARTS.set(PARTS._len-1,P = new Partition());
      return P;
    }

    // Reset for another round of minimization
    static void clear() {
      TYPE2PART.clear();
      for( Partition P : PARTS )  P.clear0();
      PARTS.clear();            // Does not delete any Parts
    }

    // Polite tracking for partitions
    private static int CNT=1;
    int _uid = CNT++;
    @Override public int getAsInt() { return _uid; }
    // All the Types in this partition
    private final Ary<Type> _ts = new Ary<>(new Type[1],0);
    // All the Type uids, touched in this pass
    private final BitSetSparse _touched = new BitSetSparse();
    // Number of new (not interned) types.
    private int _numnew;

    // All the edge labels
    private final NonBlockingHashMap<String,String> _edges = new NonBlockingHashMap<>();
    private void clear0() {
      _ts.clear();
      _numnew=0;
      assert _touched.cardinality()==0;
      _edges.clear();
    }

    // Number of Types in partition
    int len() { return _ts._len; }
    // Add type t to Partition, track the edge set
    void add( Type t) {
      if( t._hash==0 ) _numnew++;
      _ts.add(t);
      TYPE2PART.put(t._uid,this);
      var edges = DefUse.edges(t);
      if( edges != null )
        for( String s : edges )
          _edges.put(s,"");
    }
    // Delete and return the ith type.  Does not update the edges list, which
    // may contain edge labels that no longer point to any member of the part.
    Type del(int idx) {
      Type t = _ts.at(idx);
      if( t._hash==0 ) _numnew--;
      TYPE2PART.remove(t._uid);
      return _ts.del(idx);
    }
    // Get head/slot-0 Type
    Type head() { return _ts.at(0); }
    void set_head(Type newhead, Type oldhead) {
      _ts.del(newhead);         // Remove any newhead, if it exists
      _ts.set(0,newhead);       // Set newhead as The Head
      _ts.push(oldhead);        // Include oldhead in the list
    }

    // Get the partition head value for type t, if it exists, or just t
    static Type head(Type t) {
      Partition P = TYPE2PART.get(t._uid);
      return P==null ? t : P.head();
    }


    // Cause_Splits from Click thesis.
    // Original loop ordering; need to have the set of edge labels
    // Loops over all outgoing partition edges once per edge label.
    //   for-all edge labels:
    //     for-all Tx in P
    //       for-all Ty of Tx.uses[edge]
    //         assert Ty[edge]==Tx // Edge going from Y to X
    //         Py = partition(Ty)
    //         touched.set(Py);// track partitions Py
    //         Py.touched.set(Py) // track types in Py that are touched
    //   for-all Pz in touched
    //     if Pz.touched!=Pz  // did not touch them all
    //       Split(Pz,Pz.touched)
    //     clear Pz.touched
    //   touched.clear
    private static final Work<Partition> TOUCHED = new Work<>();
    void do_split() {
      assert TOUCHED.isEmpty();
      for( String edge : _edges.keySet() ) {
        boolean edge_alive=false; // Lazily reduce the edge set
        for( Type tdef : _ts ) {
          Ary<Type> tuses = DefUse.uses(edge,tdef);
          if( tuses!=null ) {
            edge_alive=true;
            for( Type tuse : tuses ) {
              Partition Puse = TYPE2PART.get(tuse._uid);
              if( Puse !=null && Puse.len() > 1 ) // Length-1 partitions cannot be split
                TOUCHED.add(Puse)._touched.tset(tuse._uid);
            }
          }
        }
        if( !edge_alive )
          _edges.remove(edge);
      }

      Partition Pz;
      while( (Pz=TOUCHED.pop())!=null ) { // For all touched partitions
        if( Pz._touched.cardinality() < Pz.len() ) { // Touched all members?
          Partition P2 = Pz.split();
          WORK.add(WORK.on(Pz) || Pz.len() > P2.len() ? P2 : Pz);
          if( Pz.len()>1 && Pz._numnew == 0 ) WORK.add(Pz);
          if( P2.len()>1 && P2._numnew == 0 ) WORK.add(P2);
        }
        Pz._touched.clear();
      }

      // See if partition has only interned Types, and has more than one.
      // Split it.
      if( len() > 1 && _numnew==0 ) {
        // Split this partition into 1-per-interned-element
        while( len()>1 ) {
          Partition P2 = malloc();
          P2.add(del(0));
          WORK.add(P2);
        }
      }
    }

    // Split a partition in two based on the _touched set.
    Partition split() {
      assert 1 <= _touched.cardinality() && _touched.cardinality() < _ts._len;
      Partition P2 = malloc();
      for( int i=0; i<_ts._len; i++ )
        if( _touched.tset(_ts.at(i)._uid) ) // Touched; move element
          P2.add(del(i--));                 // Delete from this, add to P2
      assert len() >= 1 && P2.len() >= 1;
      return P2;
    }

    @Override public String toString() { return str(new SB()).toString(); }
    SB str(SB sb) {
      sb.p('P').p(_uid).p(" #").p(len()).p(' ');
      if( len()==0 ) return sb;
      Type h = head();
      _uid(sb,h).p(' ');
      switch( h._type ) {
      case Type.TSTRUCT -> {
        sb.p("@{ ");
        for( TypeFld fld : ((TypeStruct) h).asorted_flds() )
          _uid(sb.p(fld._fld).p(":"), fld).p(' ');
        sb.unchar().p("}");
      }
      case Type.TFLD -> _uid(sb.p('.').p(((TypeFld) h)._fld).p(": "), ((TypeFld) h)._t);
      case Type.TMEMPTR -> _uid((((TypeMemPtr) h)._aliases.str(sb.p('*')).p(": ")), ((TypeMemPtr) h)._obj);
      case Type.TFUNPTR -> {
        TypeFunPtr tfp = (TypeFunPtr) h;
        _uid(_uid(tfp._fidxs.str(sb).p("{ "), tfp._dsp).p(" -> "), tfp._ret).p(" }");
      }
      case Type.TARY -> throw unimpl();
      default -> h.str(sb,null,null,false);
      }
      return sb;
    }
    private SB _uid(SB sb, Type t) { return sb.p(t._hash==0 ? '_' : ' ').p(t._uid);  }

    public static void print_parts() {
      SB sb = new SB();
      for( Partition P : PARTS ) P.str(sb).nl();
      System.out.println(sb);
    }
  }


  // Pick initial partitions for Types based on static Type properties.
  // This uses an alternative hash and equals functions.
  class SType {
    static private final NonBlockingHashMap<SType,Partition> TYPE2INITPART = new NonBlockingHashMap<>();
    static private SType KEY = new SType();

    // All types put in partitions based on static (no edges) properties:
    // Private one for interned, one for each _type, _any, and _aliases,
    // _fidxs or field names/_open/_use.  Put all partitions on worklist,
    // then repeat cause_splits.
    static Partition init_part(Type t) {
      KEY._t = t;             // Put Type in the prototype SType
      Partition P = TYPE2INITPART.get(KEY);
      if( P==null ) {         // No matching SType, so needs a new partition
        P = Partition.malloc();
        TYPE2INITPART.put(KEY,P); // Install SType to Partition
        KEY = malloc();       // Return a new prototype SType for next lookup
      }
      return P;
    }

    static private SType malloc() { return new SType(); }
    private void free() {}

    static void clear() {
      for( SType s : TYPE2INITPART.keySet() )
        s.free();
      TYPE2INITPART.clear();
    }

    // Static hash
    private Type _t;          // A prototype Type, only looking at the static properties
    @Override public int hashCode() { return _t.static_hash(); }
    @SuppressWarnings("unchecked")
    @Override public boolean equals(Object o) {
      if( this==o ) return true;
      if( !(o instanceof SType) ) return false;
      Type t2 = ((SType)o)._t;
      return _t._type == t2._type && _t.static_eq(t2);
    }
  }

  // Worklist
  Work<Partition> WORK = new Work<>();

  // Def-Use edges.  Requires def-use edges which are not part of
  // the normal types; requires a side-structure build in a pre-pass.
  // Will be iterating over all (use,edge) pairs from a def.
  class DefUse {
    static private final NonBlockingHashMapLong<NonBlockingHashMap<String,Ary<Type>>> EDGES = new NonBlockingHashMapLong<>();
    @SuppressWarnings("unchecked")
    static private final Ary<NonBlockingHashMap<String,Ary<Type>>> FREES = new Ary(new NonBlockingHashMap[1],0);
    @SuppressWarnings("unchecked")
    static private final Ary<Ary<Type>> FREES0 = new Ary(new Ary[1],0);

    // use[edge]-->>def;
    static Type add_def_use( Type use, String edge, Type def ) {
      var edges = EDGES.get(def._uid);
      if( edges==null )
        EDGES.put(def._uid,edges = malloc());
      var uses = edges.get(edge);
      if( uses==null ) edges.put(edge,uses = malloc0());
      uses.push(use);
      return null;
    }

    // Get an iterator for all the uses of a def with edge e
    static Ary<Type> uses( String e, Type def ) {
      var edges = EDGES.get(def._uid);
      return edges==null ? null : edges.get(e);
    }

    // Get the set of edge labels leading to a def
    static Set<String> edges( Type def ) {
      var edges = EDGES.get(def._uid);
      return edges==null ? null : edges.keySet();
    }

    static private NonBlockingHashMap<String,Ary<Type>> malloc() {
      return FREES.isEmpty() ? new NonBlockingHashMap<>() : FREES.pop();
    }
    static private Ary<Type> malloc0() {
      return FREES0.isEmpty() ? new Ary<>(Type.class) : FREES0.pop();
    }

    // Free all use/def edge sets
    static void clear() {
      for( var edges : EDGES.values() ) {
        for( var uses : edges.values() )
          FREES0.push(uses).clear();
        FREES.push(edges).clear();
      }
      EDGES.clear();
    }
  }


  @SuppressWarnings("unchecked")
  private static <T extends Type> T _dfa_min(T nt) {
    // Walk the reachable set and all forward edges, building a reverse-edge set.
    for( Type t : REACHABLE )  {
      if( t._hash!=0 && !t.interned() )
        t._hash=0;              // Invariant: not-interned has no hash
      if( t instanceof Cyclic )
        ((Cyclic)t).walk1( (t2,label) -> DefUse.add_def_use(t,label,t2) );
    }

    // Pick initial Partitions for every reachable Type
    for( Type t : REACHABLE )
      SType.init_part(t).add(t);

    // Put all partitions on worklist
    for( Partition P : Partition.PARTS )
      WORK.add(P);

    // Repeat until empty
    while( !WORK.isEmpty() )
      WORK.pop().do_split();

    // Walk through the Partitions, picking a head and mapping all edges from
    // head to head.
    for( Partition P : Partition.PARTS )
      if( P.head() instanceof Cyclic )
        ((Cyclic)P.head()).walk_update(Partition::head);

    // Edges are fixed, compute hash
    for( Partition P : Partition.PARTS ) if( P.head() instanceof TypeStruct ) P.head().set_hash();
    for( Partition P : Partition.PARTS ) if( P.head() instanceof TypeMemPtr ) P.head().set_hash();
    for( Partition P : Partition.PARTS ) if( P.head() instanceof TypeFunPtr ) P.head().set_hash();
    for( Partition P : Partition.PARTS )                                      P.head().set_hash();

    // Anything we make here might already be interned, at either the top-level
    // or at any intermediate point (and we might have been passed new types
    // with prior interned matches).  Replace any already interned parts.
    boolean done=false;
    while( !done ) {
      done = true;
      for( Partition P : Partition.PARTS ) {
        Type head = P.head();
        if( head instanceof Cyclic )
          ((Cyclic)head).walk_update(Partition::head);
        Type i = head.intern_lookup();
        if( i!=null && head!=i ) { done=false; P.set_head(i,head); }
      }
    }

    for( Partition P : Partition.PARTS ) {
      for( int i=1; i<P.len(); i++ )
        P._ts.at(i).free(null);
    }

    // Return the input types Partition head
    T rez = (T)Partition.TYPE2PART.get(nt._uid).head();
    Partition.clear();
    SType.clear();
    DefUse.clear();
    assert WORK.isEmpty();
    return rez;
  }

}
