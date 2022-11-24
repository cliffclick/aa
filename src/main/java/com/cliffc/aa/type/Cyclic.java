package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.Map;
import java.util.Set;
import java.util.function.IntSupplier;

import static com.cliffc.aa.AA.unimpl;

// Algorithm for minimizing a not-yet-interned graph of Types
public interface Cyclic {

  // --------------------------------------------------------------------------
  // Install a cyclic structure.  'head' is not interned and points to a
  // (possibly cyclic) graph of not-interned Types.  Minimize the graph, set
  // the hashes everywhere, check for a prior existing Type.  Return a prior,
  // or else set all the duals and intern the entire graph.

  // Also takes a Map of Types, and updates them all.  I hate this, as it
  // breaks an otherwise very clean API.  Used by cyclic type parsing.

  static <T extends Type> T install( T head ) { return install(head,null); }

  static <T extends Type> T install( T head, Map<String,Type> map ) {
    long t0 = System.currentTimeMillis();
    TypeStruct.MEETS0.clear();
    _reachable(head,true);      // Compute 1st-cut reachable
    // P.gather(); // Turn off detail profiling
    head = _dfa_min(head, map);
    _reachable(head,false);     // Recompute reachable; skip interned; probably shrinks

    // Set cyclic bits, to allow computing cyclic hashes and faster compares
    CVISIT.clear();             // Reset globals
    assert CSTACK.isEmpty();    // Reset globals
    _set_cyclic(head);

    // Install non-cyclics recursively with a DAG visit; install cyclics as a whole cycle
    CVISIT.clear();             // Reset globals
    SCC_MEMBERS.clear();        // Reset globals
    T head2 = dag_install(head, 0, null);

    // Update the mapping
    if( map != null )
      map.replaceAll((k,v) -> v.interned() ? v : v.intern_get());
    // Free anything interned to a previous Type
    while( SCC_FREE_FLDS._len>0 )
      SCC_FREE_FLDS.pop().flds_free();
    while( SCC_FREE._len>0 )
      SCC_FREE.pop().free(null);

    // Profile; return new interned cycle
    long t1 = System.currentTimeMillis();
    P.time += (t1-t0);  P.cnt++;
    return head2;
  }

  // -----------------------------------------------------------------
  // All SCCs are marked and colored (with leader color).
  // Outside SCCs, do a normal DAG recursive installation.
  // For an SCC, effectively do the whole SCC as a single lump.

  // Passed-in the current SCC color, and SCC-in-progress number.
  // The SCC depth points to an Ary of members.

  Ary<Type> SCC_FREE = new Ary<>(Type.class);
  Ary<TypeStruct> SCC_FREE_FLDS = new Ary<>(TypeStruct.class);
  Ary<Ary<Type>> SCC_MEMBERS = new Ary<Ary<Type>>(new Ary[1],0);
  private static <T extends Type> T dag_install(T t, final int scc_depth, Type scc_leader) {
    if( t.interned() ) return t; // No change to interned already
    // Visited already?
    if( CVISIT.tset(t._uid) ) {
      // If hash==0, then this is a backedge of a cycle, just return.
      // If dual!=null, then this is an old interned type, just return.
      if( t._hash==0 || t._dual!=null ) return t;
      // 't' is revisited, was interned to some old, marked freed already.  Use the old.
      T old = (T)t.intern_get();
      assert old!=null;
      return old;
    }
    Type leader = t.cyclic();
    // Increase depth if starting a new SCC
    final int scc_depth2 = scc_depth + ((leader==null || scc_leader==leader) ? 0 : 1);
    if( scc_depth2 != scc_depth ) { // Moved down to a new depth
      Ary<Type> ts = SCC_MEMBERS. atX(scc_depth2);
      if( ts==null ) SCC_MEMBERS.setX(scc_depth2,new Ary<>(Type.class));
      else ts.clear();
    }
    // Walk all children first
    t.walk_update( (fld)->dag_install(fld,scc_depth2,leader) );
    // Add self to the SCC member list
    if( leader != null )
      SCC_MEMBERS.atX(scc_depth2).push(t);

    // Not in any SCC, normal install
    if( leader==null ) {
      assert !t.interned();
      if( t instanceof TypeStruct ts ) ts.remove_dups_hashcons();
      T old = (T)t.hashcons();
      if( t!=old ) SCC_FREE.push(t);
      t=old;

    // Detect an SCC change; we just ended walking an entire SCC
    } else if( scc_leader != leader ) {
      // Just completed an entire SCC.  Hash it, install it.
      Ary<Type> ts = SCC_MEMBERS.at(scc_depth2);

      // Canonicalize TypeFlds in TypeStructs.  Changes hash so has to happen
      // before hash calc.
      for( Type c : ts )
        if( c instanceof TypeStruct tst )
          tst.remove_dups();

      // The hash has to be order-invariant, since we might visit the members
      // in a different order on a later install.  Requires 2 passes.
      long cyc_hash=0;
      for( Type c : ts )  cyc_hash ^= c.static_hash(); // Just XOR all the static hashes
      if( cyc_hash==0 ) cyc_hash = 0xcafebabe;         // Disallow zero hash
      for( Type c : ts )  c._cyc_hash = cyc_hash;      // Set cyc_hash to the same for all cycle members
      for( Type c : ts )  c._hash = c.compute_hash();  // Now compute proper hash - depends on cyc_hash plus the member specifics

      // Since all hashed (but no duals) can check for a prior intern
      T old = (T)t.intern_get();
      if( old!=null ) {
        SCC_FREE.addAll(ts);    // Free the old, return prior
        for( Type t2 : ts ) if( t2 instanceof TypeStruct ts2 ) SCC_FREE_FLDS.add(ts2);
        t=old;                  // Use the old instead of new-just-hashed
      } else {
        // Keep the entire cycle.  xdual/rdual/hash/retern
        Type.RECURSIVE_MEET++; // Stop xdual interning TypeFlds
        // Build the dual cycle, with dual leader
        for( Type c : ts ) { Type d = c._dual = c.xdual(); d._dual = c; }
        Type dleader = leader.dual();
        dleader.set_cyclic(dleader); // Dual cycle-leader, head of the dual cycle
        for( Type c : ts ) { c.rdual(); c._dual.set_cyclic(dleader); }
        // Compute the dual hash
        long dcyc_hash = 0;
        for( Type c : ts ) dcyc_hash ^= c._dual.static_hash();
        if( dcyc_hash==0 ) dcyc_hash = 0xcafebabe; // Disallow zero hash
        for( Type c : ts ) { c._dual._cyc_hash = dcyc_hash; }
        for( Type c : ts ) { c._dual._hash = c._dual.compute_hash(); }
        
        for( Type c : ts ) c.retern()._dual.retern();
        Type.RECURSIVE_MEET--; // Allow xdual to intern TypeFlds
        for( Type c : ts )     // Now that all fields are interned, we can intern the TypeFld[]
          if( c instanceof TypeStruct tst ) {
            tst.remove_dups_hashcons();
            tst._dual.remove_dups_hashcons();
          }
      }
    } // else same SCC, no change
    return t;
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
  private static void _set_cyclic(Type t ) {
    if( t.dual()!=null ) return; // Already interned
    if( CVISIT.tset(t._uid) ) { // If visiting again... have found a cycle t->....->t
      // All on the stack are flagged as being part of a cycle
      Type leader = t.cyclic();
      int i=CSTACK._len-1;
      while( i >= 0 && CSTACK.at(i)!=t && !(leader!=null && CSTACK.at(i).cyclic()==leader) )
        i--;
      if( i== -1 ) return;  // Due to multi-edges, we might not find if dupped, so just ignore
      // Set the cyclic leader
      leader = CSTACK.at(i);
      for( int j=i; j < CSTACK._len; j++ )
        CSTACK.at(j).set_cyclic(leader);
      return;
    }
    CSTACK.push(t);             // Push on stack, in case a cycle is found
    t.walk((fld,ignore) -> _set_cyclic(fld));
    CSTACK.pop();               // Pop, not part of another's cycle
  }

  // -----------------------------------------------------------------
  // Reachable collection of not-interned Types, plus if also_interned
  // an "edge" of interned Types to help the partition splitter.
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
      assert t.interned() || t instanceof Cyclic;
      if( !t.interned() && t instanceof Cyclic )
        t.walk((tc,ignore) -> {
            if( !ON_REACH.tset(tc._uid) && (!tc.interned() || also_interned) )
              REACHABLE.push(tc);
          } );
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
      TYPE2PART.clear(true);
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
      _edges.clear(true);
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
        for( TypeFld fld : ((TypeStruct) h) )
          _uid(sb.p(fld._fld).p(":"), fld).p(' ');
        sb.unchar().p("}");
      }
      case Type.TFLD    -> _uid(sb.p('.').p(((TypeFld) h)._fld).p(": "), ((TypeFld) h)._t);
      case Type.TMEMPTR -> _uid((((TypeMemPtr) h)._aliases.str(sb.p('*')).p(": ")), ((TypeMemPtr) h)._obj);
      case Type.TFUNPTR -> {
        TypeFunPtr tfp = (TypeFunPtr) h;
        _uid(_uid(tfp.fidxs().str(sb).p("{ "), tfp.dsp()).p(" -> "), tfp._ret).p(" }");
      }
      case Type.TARY -> throw unimpl();
      default -> h.str(sb, false, false);
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
    @Override public int hashCode() {
      long hash = _t.static_hash();
      assert hash!=0;
      return (int)((hash>>32)|hash);
    }
    @SuppressWarnings("unchecked")
    @Override public boolean equals(Object o) {
      if( this==o ) return true;
      if( !(o instanceof SType st) ) return false;
      Type t2 = st._t;
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
    static void add_def_use(Type use, String edge, Type def ) {
      var edges = EDGES.get(def._uid);
      if( edges==null )
        EDGES.put(def._uid,edges = malloc());
      var uses = edges.get(edge);
      if( uses==null ) edges.put(edge,uses = malloc0());
      uses.push(use);
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
  private static <T extends Type> T _dfa_min(T nt, Map<String,Type> map) {
    // Walk the reachable set and all forward edges, building a reverse-edge set.
    for( Type t : REACHABLE )  {
      assert (t._hash==0) == (t.dual()==null);  // Invariant: not-interned has no hash
      if( t instanceof Cyclic )
        t.walk( (t2,label) -> DefUse.add_def_use(t,label,t2) );
    }

    // Pick initial Partitions for every reachable Type
    for( Type t : REACHABLE )
      SType.init_part(t).add(t);

    // Put all partitions on worklist
    for( Partition P : Partition.PARTS )
      WORK.add(P);

    // Repeat until empty, partition splitting.
    while( !WORK.isEmpty() )
      WORK.pop().do_split();

    // Walk through the Partitions, picking a head and mapping all edges from
    // head to head.
    for( Partition P : Partition.PARTS )
      if( P.head() instanceof Cyclic )
        P.head().walk_update(Partition::head);

    // Update an unrelated mapping of types to their partition heads
    if( map!=null )
      map.replaceAll((k,v) -> {
          Partition P = Partition.TYPE2PART.get(v._uid);
          return P==null ? v : P.head();
        });

    // Free all the Types declared as replicas
    for( Partition P : Partition.PARTS )
      for( int i=1; i<P.len(); i++ ) // Skip the head in slot 0
        if( !P._ts.at(i).interned() )
          P._ts.at(i).free(null);

    // Return the input types Partition head
    // Reset statics for the next call.
    T rez = (T)Partition.TYPE2PART.get(nt._uid).head();
    Partition.clear();
    SType.clear();
    DefUse.clear();
    assert WORK.isEmpty();
    return rez;
  }

  // Everything that is cycle-equals is in the same partition
  static boolean check() {
    int err=0;
    for( int i=0; i<REACHABLE._len; i++ ) {
      Type t1 = REACHABLE.at(i);
      Partition p1 = Partition.TYPE2PART.get(t1._uid);
      for( int j=i+1; j<REACHABLE._len; j++ ) {
        Type t2 = REACHABLE.at(j);
        Partition p2 = Partition.TYPE2PART.get(t2._uid);
        if( p1!=p2 && t1.cycle_equals(t2) )
          System.err.println("Err "+(err++)+" T"+t1._uid+p1+" != T"+t2._uid+p2);
      }
    }
    return err==0;
  }

  // Report a path-difference between two Types.  Useful for debugging large types.
  final class Link { Link _nxt; int _d; Type _t0,_t1;
    static Link min(Link l0, Link l1) {
      if( l0==null ) return l1;
      if( l1==null ) return l0;
      return l0._d<l1._d ? l0 : l1;
    }
    SB str(SB sb) {
      if( _t0==null ) return sb.p('_');
      throw unimpl();
    }
    static SB str(SB sb, NonBlockingHashMapLong<Link> links) {
      for( long key : links.keySetLong() ) {
        sb.p("{").p(key>>32).p(',').p(key&0xFFFFFFFFL).p("} = ");
        links.get(key).str(sb).nl();
      }
      return sb;
    }
  }
  static Link path_diff(Type t0, Type t1) {
    NonBlockingHashMapLong<Link> links = new NonBlockingHashMapLong<>();
    Link best = _path_diff(t0,t1,links);
    return best;
  }
  static long duid(Type t0, Type t1) { return (((long)t0._uid)<<32)|t1._uid; }

  // --------------------------------------------------------------------------
  // Returns null if no diff, otherwise returns the shortest path to a diff.
  @SuppressWarnings("unchecked")
  static Link _path_diff(Type t0, Type t1, NonBlockingHashMapLong<Link> links) {
    if( t0==t1 ) return null;
    long duid = duid(t0,t1);
    Link lk = links.get(duid), diff=null;
    if( lk!=null ) return lk;   // Been there, done that
    lk = new Link();            // Placeholder
    links.put(duid,lk);         // Stop recursion
    if( t0.getClass() == t1.getClass() && t0 instanceof Cyclic cyc &&
        t0.static_eq(t1) ) {
      // Must recursively ask the question again
      diff = cyc._path_diff0(t1,links);
      if( diff==null || diff._t0==null ) return lk; // No difference
    }
    lk._nxt = diff;
    lk._d = diff==null ? 0 : diff._d+1;
    lk._t0=t0;
    lk._t1=t1;
    return lk;
  }

  abstract Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links);

  // --------------------------------------------------------------------------
  class Prof {
    long cnt=0, time=0;
    int hit;                    // Hit on prior cycle type
    int clarge_sum=0, clarge_cnt=0; int [] chisto = new int[ 32];
    int ilarge_sum=0, ilarge_cnt=0; int [] ihisto = new int[ 32];
    int rlarge_sum=0, rlarge_cnt=0; int [] rhisto = new int[128];
    void gather() {
      if( (cnt&63)==0 ) print();
      int icnt=0, ccnt=0;
      for( Type t : REACHABLE ) {
        if( t.interned() ) icnt++;
        if( t.cyclic()!=null ) ccnt++;
      }
      if( icnt<ihisto.length ) ihisto[icnt]++;
      else { ilarge_sum += icnt; ilarge_cnt++; }
      if( ccnt<chisto.length ) chisto[ccnt]++;
      else { clarge_sum += icnt; clarge_cnt++; }
      int rcnt = REACHABLE._len;
      if( rcnt<rhisto.length ) rhisto[rcnt]++;
      else { rlarge_sum += rcnt; rlarge_cnt++; }
    }
    void print() {
      SB sb = new SB();
      sb.p("Prof DFA; ");
      sb.p("Avg time ").p((double)time/cnt).p("msec").nl();
      sb.p("Cyclic, #large:").p(clarge_cnt).p(" ");
      for( int i=0; i<chisto.length; i++ )
        if( chisto[i]!=0 )
          sb.p("hist["+i+"]="+chisto[i]+",");
      sb.unchar().nl();
      sb.p("Intern, #large:").p(ilarge_cnt).p(" ");
      for( int i=0; i<ihisto.length; i++ )
        if( ihisto[i]!=0 )
          sb.p("hist["+i+"]="+ihisto[i]+",");
      sb.unchar().nl();
      sb.p("REACH, #large:").p(rlarge_cnt).p(" ");
      for( int i=0; i<rhisto.length; i++ )
        if( rhisto[i]!=0 )
          sb.p("hist["+i+"]="+rhisto[i]+",");
      sb.unchar().nl();
      System.out.println(sb);
    }
  }
  Prof P = new Prof();


}
