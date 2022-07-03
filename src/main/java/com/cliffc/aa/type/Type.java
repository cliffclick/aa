package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.function.BinaryOperator;
import java.util.function.IntSupplier;

import static com.cliffc.aa.AA.unimpl;

/** an implementation of language AA
 */

// C2-style type system, with Meet & Dual.

// This is a symmetric complete bounded (ranked) lattice.
// Also the meet is commutative and associative.
// The lattice has a dual (symmetric), and join is ~(~x meet ~y).
// See https://en.wikipedia.org/wiki/Lattice_(order).

// Symmetric around the centerline of constants.  Fixed height, so a finite
// count of Meet stabilizes; a unique All (Bottom; no known value) and due to
// symmetry a unique Any (Top, all values simultaneously).  Supports function
// types, various kinds of numeric ranges, nil, tuples and structs, objects,
// and memory.
//
// During program typing, always keeping the "loosest" possible program and if
// this program still types as 'Any' then the program is ambiguous.  'All'
// represents a type conflict.
//
// ASCII-Grams of Type Lattices
//
// Ints:   ~int64 -> ~int32 -> ~int16 -> ~int8 -> ~int1 -> {...-3,-2,-1,0,1,2,3,...} -> int1 -> int8 -> int16 -> int32 -> int64
//                /---^     /--^                                                                          \------v     \---v
// Floats: ~flt64 -> ~flt32 ----------------------------> {... -pi,-0.1,0,0.1,pi, ... } ----------------------> flt32 -> flt64
// int{1,8,16} all inject in flt32; int32 injects in flt64.  Small integer
// constants as floats inject into the integers.
//
// Pointers are everywhere nullable; they always support a {oop+null, oop,
// null, oop&null} set of choices, where oop+null and oop&null are duals.
// Structs are OOPS with an infinite list of values and a delta-set of named
// field exceptions.  The fields are dualed structurally.  High structs default
// to ANY and low to ALL.  Tuples are structs with fields named "0", "1", etc.
//
// Because the meet is commutative, associative, symmetric, the following holds:
//
//     (forall X, join X) === ~(forall X, meet ~X)
//
// ===========================================================================
//
// A Treatise on NIL
//
// I want to have a distinguished NIL-type in the language - too obvious, too
// useful.  Hence "i=0" or "ptr=0" or "ptr ? s1 : s2" all use the concept of
// nil.  However, having a single type which can be both an integer and a
// pointer breaks the major Type Lattice property.  Basically if nil can be
// used to "cross" between Integers and Pointers (or Fun Pointers, Floats, etc)
// then the Type system is no longer a Lattice and all sorts of havoc ensues.
//
// Over the past 1.5yrs I've tried every possible combination of things I can
// do with nil that also lets me keep it in the language and used in both
// integer and pointer contexts, but also in the Lattice.  The Type code is
// full of train-wreck leftovers from various attempts.
//
// Example:
//    ~int  == int.dual() (the high ints)
//    *str? == a nil-able pointer to a string
// A "NIL" such that ~int.meet(NIL) == NIL, but also NIL.meet(*str?) == (*str?)
// seems highly desirable... and crosses between ints and string-pointers.

// Cast-not-nil (after a if-test for nil) in dying (not dead) code often sees
// nil inputs.  Casts do a JOIN on their input - so we might see e.g.
// nil.join(*str).  The problem is, the nil can drop to an int before the Cast
// goes dead.  Thus the Cast computes int.join(*str).  Since nil.isa(int) the
// Cast inputs drop monotonically... so the output should also.  Thus
// nil.join(*str).isa(int.join(*str)).  This is a standard symmetry
// property and is one of the major Type system asserts... and it doesn't hold.

// nil.isa(int) == TRUE          ; the nil is treated as a TypeInt.ZERO
// nil.join(*str) == *[0+4+]str? ; the nil is treated as a TypeMemPtr.NIL.
// int.join(*str) == nScalar     ; Nothing in common
// *[0+4+]str?.isa(nScalar) == FALSE!!!!! ; Crossing-nil has failed again...

// Tried a nil is in the Type system, but OUT of the Lattice.  At any given use
// point the nil collapses exactly one of the more refined nils (TypeInt.ZERO,
// TypeMemPtr.NIL, etc) but until then it is an undistinguished nil.

// Current solution is that nil 2 extra bits on all Types, with 4 states:
// AND-nil, OR-nil, NOT-nil, YES-nil.  YES-nil is just nil, but with all the
// other Type info present to preserve the lattice properties.  In this
// solution, the old nScalar becomes Scalar-NOT-NIL.  Also (unlike most
// previous attempts) we can represent ~Scalar-AND-NIL: something which
// definitely can be nil, but we're not yet sure if it is a e.g. pointer
// (TypeMemPtr) or integer (TypeInt).

public class Type<T extends Type<T>> implements Cloneable, IntSupplier {
  static private int CNT=1;
  public int _uid;       // Unique ID, will have gaps, used to uniquely order Types
  public long _hash, _cyc_hash; // Hash for this Type; built recursively except around cycles
  public byte _type;            // Simple types use a simple enum
  private Type _cyclic;  // Type is cyclic, and this is the canonical cycle leader.
  T _dual; // All types support a dual notion, eagerly computed and cached here

  private static int _uid() { return CNT++; }
  @Override public int getAsInt() { return _uid; }
  T init() { _cyclic=null; return (T)this; }

  // ----------
  // Type is cyclic.
  // The leader of the Strongly Connected Component this Type is part of or
  // null.  The head is always alive, and always uses the minimal Type UID, and
  // is effectively the SCC "color".  Two SCCs might abutt with only a pointer
  // between them (no Type), and the "color" can be used to tell when it's safe
  // to stop a cyclic-equality check or limit a cycle-hash.
  Type cyclic() {
    Type c = _cyclic;
    if( c==null ) return null;
    if( c._cyclic == c ) return c;
    // Perform a Union-Find rollup, required when lazy setting nested cycles
    while( c._cyclic != c ) c = c._cyclic; // Find top
    Type x = this;
    while( x != c ) { Type old = x._cyclic; x._cyclic = c; x=old; } // Rollup
    return c;
  }
  void set_cyclic(Type leader) {
    // There are 3 UIDs here, pick the smallest.
    // - this  ._uid  but only if _cyclic==null
    // - leader._uid
    // - cyclic._uid
    if( _cyclic==null ) _cyclic = this;
    // Now there are only two: _cyclic & leader
    Type c = cyclic();          // UF fold
    Type l = leader.cyclic();   // UF fold
    if( c._uid < l._uid ) l._cyclic = c;
    else                  c._cyclic = l;
  }

  // ----------
  // The hashcode.  Built recursively from static_hash() and parts, except at
  // cycles.  In Strongly Connected Component, all members contribute their
  // static_hash() in an order-independent way (because I've no idea which
  // member will be the starting point of a random SCC) to produce a cyclic
  // hash.  Then each member mixes the cyclic_hash with its own static_hash.
  // Zero if not set.
  @Override public final int hashCode( ) {
    assert _hash!=0;
    long hash = _hash;
    int ihash = 0;              // Mix bits
    while( ihash==0 ) { ihash = (int) ((hash >> 32) ^ hash); hash >>>= 1; }
    return ihash;
  }
  // Static properties hashcode, no edges.
  long static_hash() { return (_type<<1)|1; }

  // Compute the hash and return it.  Use a child hash, if they have one, or
  // recursively compute the child's hash.  Expects all children to have a hash.
  long compute_hash() {
    // Mixing here has to be child-visit-order invariant, or I have to enforce
    // a child-visit-order on TypeStruct (alpha-sorted field names).  Currently,
    // using XOR as an order-invariant mixer.
    long hash = lwalk( (fld,str) -> fld._cyc_hash ^ str.hashCode(),
                       (hash0,hash1) -> hash0 ^ hash1 );
    return Util.mix_hash(hash,static_hash());
  }

  // ----------
  // Is anything equals to this?
  @Override public boolean equals( Object o ) {
    if( this == o ) return true;
    return (o instanceof Type t) && _type==t._type;
  }
  // Static properties equals; edges are IGNORED.  Already known to be the same
  // class and not-equals.
  boolean static_eq(T t) { return equals(t); }
  // Full cyclic equals.  For interned types can use simple ptr-equality (which
  // is the whole point of interning).  During interning must walk both Types
  // edges and confirm they have the same structure.
  public boolean cycle_equals( Type t ) {
    assert is_simple();         // Overridden in subclasses
    return _type==t._type;
  }

  // ----------
  // Walk and apply a map and a reduce.
  // Does not guard against cycles.
  interface TypeStrMap { TypeMemPtr map(Type t, String s); }
  public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) { /*No outgoing fields*/return null; }

  // Walk and apply a map.  No return, just for side-effects.
  // Does not guard against cycles.
  interface TypeStrRun { void run(Type t, String s); }
  public void walk( TypeStrRun map ) {/*No outgoing fields*/}

  // Map and replace all child types.  Does not guard against cycles.
  // Example:
  //          [fidx]{    dsp  ->     ret   }
  //          cyclic.walk_update( child_type -> map(child_type) );
  //          [fidx]{map(dsp) -> map(ret) }
  interface TypeMap { Type map(Type t); }
  public void walk_update( TypeMap map ) {/*No outgoing fields*/}

  interface LongStringFunc { long run(Type t, String s); }
  interface LongOp { long run(long l0, long l1); }
  public long lwalk( LongStringFunc map, LongOp reduce ) { return 0xcafebabedeadbeefL; }

  // ----------
  // In order to handle recursive printing, this is the only toString call in
  // the Type hierarchy.  Instead, subtypes override 'str(...)' where the extra
  // args stop cycles (VBitSet) or sharpen pointers (TypeMem), or optimize
  // printing strings (SB).

  // toString is called on a single Type in the debugger, and prints debug-info.
  @Override public final String toString() { return str(new SB(), true, false).toString(); }
  // Nice, REPL-friendly and error-friendly dump.  Debug flag dumps, e.g. raw
  // aliases and raw fidxs.  Non-debug dumps are used in ErrMsg.  Many debug
  // dumps use this version, and intersperse types with other printouts in the
  // same SB.  This is the 'base' printer, as changing this changes behavior.
  public final SB str( SB sb, boolean debug, boolean indent ) {
    NonBlockingHashMapLong<String> dups = new NonBlockingHashMapLong<>();
    VBitSet bs = new VBitSet();
    _str_dups(bs, dups, new UCnt());
    return _str(bs.clr(), dups, sb, debug, indent );
  }
  static class UCnt { int _fld, _tmp, _tfp, _ts; }

  // The debug printer must have good handling of dups and cycles - on
  // partially-built types.  It can depend on the UID but not on, e.g., all
  // fields being filled, or the types being interned or having their hash.
  // Walk the entire reachable set of types and gather the dups, and come up
  // with a nice name for each dup.
  void _str_dups(VBitSet visit, NonBlockingHashMapLong<String> ignore, UCnt ucnt) { visit.tset(_uid); }

  // Internal tick of tick-tock printing
  final SB _str( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _hash==0 ) sb.p("!!!");
    String s = dups.get(_uid);
    if( s!=null ) {
      sb.p(s);                  // Pretty name
      if( visit.tset(_uid) ) return sb; // Pretty name got defined before
      sb.p(':');                // pretty name is defined here
    }
    return _str0(visit,dups,sb,debug,indent);
  }

  // Internal tock of tick-tock printing
  SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) { return sb.p(STRS[_type]); }

  // True if type is complex to print, and should indent when printing a Type
  final boolean _str_complex(VBitSet visit, NonBlockingHashMapLong<String> dups) {
    if( visit.test(_uid) && dups.containsKey(_uid) ) return false;
    return _str_complex0(visit,dups);
  }
  boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) { return false; }

  // Shallow array compare, using '==' instead of 'equals'.  Since elements are
  // interned, this is the same as 'equals' except asymptotically faster unless
  // there is a type-cycle, then infinitely faster.
  public static boolean eq( Type[] t0, Type[] t1 ) {
    if( t0==t1 ) return true;
    if( t0==null || t1==null ) return false;
    if( t0.length != t1.length ) return false;
    for( int i=0; i<t0.length; i++ )
      if( t0[i] != t1[i] )
        return false;
    return true;
  }

  // Construct a simple type, possibly from a pool
  static Type make(byte type) { return POOLS[type].malloc().init().hashcons_free(); }
  public T free(T t2) { return (T)POOLS[_type].free(this,t2); }
  T hashcons_free() {
    T t2 = hashcons();
    return this==t2 ? t2 : free(t2);
  }

  // ----------------------------------------------------------
  // Hash-Cons - all Types are interned in this hash table.  Thus, an equality
  // check of a (possibly very large) Type is always a simple pointer-equality
  // check, except during construction and intern'ing.
  //private static final ConcurrentHashMap<Type,Type> INTERN = new ConcurrentHashMap<>();
  private static final NonBlockingHashMap<Type,Type> INTERN = new NonBlockingHashMap<>();
  public static int RECURSIVE_MEET;    // Count of recursive meet depth
  T hashcons() {
    if( RECURSIVE_MEET>0 && this instanceof Cyclic )
      return (T)this; // Might be a cycle, requiring Cyclic.install.  Fail now.
    _hash = _cyc_hash = compute_hash(); // Set hash
    T t2 = (T)intern_get();     // Lookup
    if( t2!=null ) {            // Found prior
      assert t2._dual != null;  // Prior is complete with dual
      assert this != t2;        // Do not hashcons twice, should not get self back
      return t2;                // Return prior
    }
    // Not in type table
    _dual = null;                // No dual yet
    INTERN.put(this,this);       // Put in table without dual
    //Util.hash_quality_check_per(INTERN,"INTERN");
    T d = xdual();               // Compute dual without requiring table lookup, and not setting name
    d._hash = d._cyc_hash = d.compute_hash();  // Set dual hash
    _dual = d;
    if( this==d ) return d;      // Self-symmetric?  Dual is self
    assert !equals(d);           // Self-symmetric is handled by caller
    assert d._dual==null;        // Else dual-dual not computed yet
    assert d.intern_get()==null;
    d._dual = (T)this;
    INTERN.put(d,d);
    return (T)this;
  }
  final T retern( ) {
    assert _dual._dual == this;
    assert _hash != 0;
    assert INTERN.get(this)==null;
    INTERN.put(this,this);
    assert INTERN.get(this)==this;
    //Util.hash_quality_check_per(INTERN,"INTERN");
    return (T)this;
  }

  // Fast, does not check the hash table, just the hash & dual
  boolean interned() { return _hash!=0 && _dual!=null; }
  // Slow, actually probes the hash table.
  boolean un_interned() { return _hash == 0 || intern_get() != this; }
  Type intern_get() {
    //Util.reprobe_quality_check_per(INTERN,"INTERN");
    return INTERN.get(this);
  }
  public static int intern_size() { return INTERN.size(); }
  public static int intern_capacity() { return INTERN.len(); }
  public static boolean intern_check() {
    int errs=0;
    for( Type k : INTERN.keySet() ) {
      Type v = INTERN.get(k);
      if( !k.intern_check0(v) ) {
        System.out.println("INTERN_CHECK FAIL: "+k._uid+":"+k+" vs "+v._uid+":"+v);
        errs++;
      }
    }
    return errs==0;
  }
  private boolean intern_check0(Type v) {
    if( this != v || _dual==null || _dual._dual!=this ) return false;
    if( !(this instanceof Cyclic) && compute_hash()!=_hash ) return false;
    return intern_check1();
  }
  boolean intern_check1() { return true; }
  // Debugging helper
  static Type intern_find(int uid) {
    for( Type k : INTERN.keySet() )
      if( k._uid==uid )
        return k;
    return null;
  }

  // ----------------------------------------------------------
  // Simple types are implemented fully here.  "Simple" means: the code and
  // type hierarchy are simple, not that the Type is conceptually simple.
  static final byte TALL    = 0; // Bottom
  static final byte TANY    = 1; // Top
  static final byte TCTRL   = 2; // Ctrl flow bottom
  static final byte TXCTRL  = 3; // Ctrl flow top (mini-lattice: any-xctrl-ctrl-all)
  static final byte TSIMPLE = 4; // End of the Simple Types
  public boolean is_simple() { return _type < TSIMPLE; }
  private static final String[] STRS = new String[]{"all","any","Ctrl","~Ctrl"};
  // Nillable Scalars; all possible finite types that fit in a machine
  // register; includes pointers (to functions, to structs), ints, floats;
  // excludes state of Memory and Ctrl.  Scalars are stateless and "free" to
  // make copies.
  static final byte TNIL    = 5; // Scalars, nil
  static final byte TINT    = 6; // All Integers, including signed/unsigned and various sizes; see TypeInt
  static final byte TFLT    = 7; // All IEEE754 Float Numbers; 32- & 64-bit, and constants and duals; see TypeFlt
  static final byte TRPC    = 8; // Return PCs; Continuations; call-site return points; see TypeRPC
  static final byte TMEMPTR = 9; // Memory pointer type; a collection of Alias#s
  static final byte TFUNPTR =10; // Function pointer, refers to a collection of concrete functions
  static final byte TNILABLE=11;
  public boolean is_nil() { return _type < TNILABLE; }
  // Collections of Scalars, Memory, Fields.  Not Nilable.
  static final byte TSTRUCT =12; // Memory Structs; tuples with named fields
  static final byte TTUPLE  =13; // Tuples; finite collections of unrelated Types, kept in parallel
  static final byte TARY    =14; // Tuple of indexed fields; only appears in a TSTRUCT
  static final byte TFLD    =15; // Fields in structs
  static final byte TMEM    =16; // Memory type; a map of Alias#s to TOBJs
  static final byte TLAST   =17; // Type check

  // Object Pooling to handle frequent (re)construction of temp objects being
  // interned.  This is a performance hack and a big one: big because its
  // invasive, big because the performance gain is dramatic.  The hash-cons'ing
  // INTERN table has an extremely high hit rate and this hack avoids the high
  // volume allocation (and constant hardware cache misses and memory bandwidth
  // costs) associated with the constant creation and interning of Types.

  // This means most Type fields are "effectively final" instead of final: they
  // get cleared upon free, and modified when pull from the free list.  Once
  // the object interns, the fields are "effectively final".  During construction
  // of cyclic types, some objects are pulled from the free list, partially
  // initialized, used to build a cycle, then have some fields set (sometimes
  // more than once) to close the cycle.  However, once a Type is interned, its
  // fields are forever more "final".
  static final Pool[] POOLS = new Pool[TLAST];
  static class Pool {
    private int _malloc, _free, _pool;
    int _clone;                 // Allow TypeStruct a personal copy
    private final Ary<Type> _frees;
    private final Type _gold;
    Pool(byte t, Type gold) {
      gold._type = t;
      _gold=gold;
      _frees= new Ary<>(new Type[1],0);
      POOLS[t] = this;
    }
    <T extends Type> T malloc() {
      T t;
      if( _frees.isEmpty() ) {
        _malloc++;              // Make fresh
        try { t = (T)_gold.clone(); t._uid = _uid(); }
        catch( CloneNotSupportedException ignore ) {throw new RuntimeException("shut java up about not clonable");}
      } else {
        _pool++;                // Pull a from free pool
        t = (T)_frees.pop();
      }
      return t;                 // Set breakpoints here to find a uid
    }
    <T extends Type> T free(T t1, T t2) {
      t1._dual = null;   // Too easy to make mistakes, so zap now
      t1._hash = t1._cyc_hash = 0;      // Too easy to make mistakes, so zap now
      _frees.push(t1);   // On the free list
      _free++;
      assert _frees._len<1000; // Basically asserting we get Types from Pool.malloc and not by normal allocation
      return t2;
    }
  }

  // All the simple type pools
  static {
    for( int i=0; i<TSIMPLE; i++ )
      POOLS[i]=new Pool((byte)i,new Type());
  }

  protected T _copy() {
    POOLS[_type]._clone++;  POOLS[_type]._malloc--; // Move the count from malloc to clone
    return POOLS[_type].malloc();
  }

  // Overridable clone method.  Not interned.
  T copy() { assert is_simple(); return _copy(); }

  public  static final Type ALL    = make( TALL   ); // Bottom
  public  static final Type ANY    = make( TANY   ); // Top
  public  static final Type CTRL   = make( TCTRL  ); // Ctrl
  public  static final Type XCTRL  = make(TXCTRL  ); // Ctrl

  // Collection of sample types for checking type lattice properties.
  private static final Type[] TYPES = new Type[]{ALL,CTRL};

  // The complete list of primitive types that are disjoint and also is-a
  // SCALAR; nothing else is a SCALAR except what is on this list (or
  // subtypes).  Useful when type-specializing functions to break SCALAR args
  // into a concrete list of specific types.  Specifically excludes e.g.
  // TypeTuple - these may be passed as a scalar reference type in the future
  // but for now Tuples explicitly refer to multiple values, and a SCALAR is
  // exactly 1 value.
  private static Type[] SCALAR_PRIMS;

  // Simplify pointers (lose what they point at).
  public Type simple_ptr() { return this; }

  // Return cached dual
  public final T dual() { return _dual; }

  // Compute dual right now.  Overridden in subclasses.
  T xdual() { return POOLS[_type^1].malloc(); }
  void rdual() { assert _dual!=null; }

  // ----------------------------------------------------------
  // Memoize meet results
  private static class Key {
    static Key K = new Key(null,null);
    static NonBlockingHashMap<Key,Type> INTERN_MEET = new NonBlockingHashMap<>();
    Key(Type a, Type b) { _a=a; _b=b; }
    Type _a, _b;
    @Override public int hashCode() {
      long hash = (Util.rot(_a._hash,15)^_b._hash);
      return (int)((hash>>32)^hash);
    }
    @Override public boolean equals(Object o) { return _a==((Key)o)._a && _b==((Key)o)._b; }
    @Override public String toString() { return "("+_a+","+_b+")"; }
    static Type get(Type a, Type b) {
      K._a=a;
      K._b=b;
      //Util.reprobe_quality_check_per(INTERN_MEET,"INTERN_MEET");
      return INTERN_MEET.get(K);
    }
    static void put(Type a, Type b, Type mt) {
      INTERN_MEET.put(new Key(a,b),mt);
      // Uncomment to check hash quality.
      //Util.hash_quality_check_per(INTERN_MEET,"INTERN_MEET");
    }
  }

  // Compute the meet
  public final Type meet( Type t ) {
    // Short cut for the self case
    if( t == this ) return this;
    // Short-cut for seeing this meet before
    Type mt = Key.get(this,t);
    if( mt != null ) return mt;
    // Compute meet without filtering
    mt = ymeet(t);
    // Record this meet, to short-cut next time
    if( RECURSIVE_MEET == 0 )   // Only not mid-building recursive types;
      Key.put(this,t,mt);
    return mt;
  }

  // Compute meet without further filtering
  private Type ymeet( Type t ) {
    // Same-type is always safe in the subclasses
    if( _type==t._type ) return xmeet(t);

    // "Triangulate" the matrix and cut in half the number of cases.
    // Reverse; xmeet 2nd arg is never "is_simple" and never equal to "this".
    if(   is_simple() ) return this.xmeet(t   );
    if( t.is_simple() ) return t   .xmeet(this);
    // Triangulate on is_nil without being the same class
    if( is_nil() && t.is_nil() ) {
      TypeNil t0 = (TypeNil)this;
      TypeNil t1 = (TypeNil)t   ;
      if( t0._type==TNIL ) return t0.nmeet(t1); // LHS is TypeNil directly
      if( t1._type==TNIL ) return t1.nmeet(t0);
      return t0.cross_nil(t1);  // Mis-matched TypeNil subclasses
    }
    // Spray TypeNil across fields in a TypeStruct
    if( this instanceof TypeNil tn && t    instanceof TypeStruct ts ) return ts.nmeet(tn);
    if( t    instanceof TypeNil tn && this instanceof TypeStruct ts ) return ts.nmeet(tn);
    return Type.ALL;        // Mixing 2 unrelated types not subclassing TypeNil
  }


  // Compute meet right now.  Overridden in subclasses.
  // Handles cases where 'this.is_simple()' and unequal to 't'.
  // Subclassed xmeet calls can assert that '!t.is_simple()'.
  protected Type xmeet(Type t) {
    assert is_simple(); // Should be overridden in subclass
    // ANY meet anything is thing; thing meet ALL is ALL
    if( _type==TALL || t._type==TANY ) return this;
    if( _type==TANY || t._type==TALL ) return    t;
    // 'this' is {CTRL,XCTRL}
    if( !t.is_simple() ) return ALL;
    // 't' is {CTRL,XCTRL}
    if( _type==TCTRL || t._type==TCTRL ) return CTRL;
    return XCTRL;
  }

  // By design in meet, args are already flipped to order _type, which forces
  // symmetry for things with badly ordered _type fields.  The question is
  // still interesting for other orders.
  private boolean check_commute( Type t, Type mt ) {
    if( t==this ) return true;
    if( is_simple() && !t.is_simple() ) return true; // By design, flipped the only allowed order
    Type mt2 = t.meet(this);   // Reverse args and try again

    if( mt==mt2 ) return true;
    System.out.println("Meet not commutative: "+this+".meet("+t+")="+mt+",\n but "+t+".meet("+this+")="+mt2);
    return false;
  }
  // A & B = MT
  // Expect: ~A & ~MT == ~A
  // Expect: ~B & ~MT == ~B
  private boolean check_symmetric( Type t, Type mt ) {
    if( t==this ) return true;
    Type ta = mt._dual.meet(t._dual);
    Type tb = mt._dual.meet(  _dual);
    if( ta==t._dual && tb==_dual ) return true;
    System.err.print("("+this+" & "+t+")=="+mt+" but \n("+mt._dual+" & ");
    if( ta!=t._dual ) System.err.println(t._dual+")=="+ta+" \nwhich is not "+t._dual);
    else              System.err.println(  _dual+")=="+tb+" \nwhich is not "+  _dual);
    return false;
  }

  public Type join( Type t ) { return dual().meet(t.dual()).dual(); }

  // True if 'this' isa/subtypes 't'.  E.g. Int32-isa-Int64, but not vice-versa
  // E.g. ANY-isa-XSCALAR; XSCALAR-isa-Int(Any); Int(Any)-isa-Int(3)
  public boolean isa( Type t ) { return meet(t)==t; }

  // Report OOB based on shallowest OOB component.
  public Type       oob( ) { return oob(ALL); }
  public Type       oob(Type       e) { return above_center() ? e.dual() : e; }
  public TypeStruct oob(TypeStruct e) { return above_center() ? e.dual() : e; }
  public TypeMem    oob(TypeMem    e) { return above_center() ? e.dual() : e; }
  public TypeMemPtr oob(TypeMemPtr e) { return above_center() ? e.dual() : e; }
  public T oob(boolean b) { return b ? dual() : (T)this; }

  // Parser init
  public static void init0( HashMap<String,Type> types ) { TypeNil.init0(types); }

  private static Ary<Type> ALL_TYPES; // Used for tests
  public static Ary<Type> ALL_TYPES() {
    if( ALL_TYPES != null ) return ALL_TYPES;
    Ary<Type> ts = new Ary<>(new Type[1],0);
    concat(ts,Type      .TYPES);
    concat(ts,TypeNil   .TYPES);
    concat(ts,TypeAry   .TYPES);
    concat(ts,TypeInt   .TYPES);
    concat(ts,TypeFlt   .TYPES);
    concat(ts,TypeMemPtr.TYPES);
    concat(ts,TypeFunPtr.TYPES);
    concat(ts,TypeRPC   .TYPES);
    concat(ts,TypeMem   .TYPES);
    concat(ts,TypeStruct.TYPES);
    concat(ts,TypeTuple .TYPES);
    // Partial order Sort, makes for easier tests later.  Arrays.sort requires
    // a total order (i.e., the obvious Comparator breaks the sort contract),
    // so we hand-roll a simple bubble sort.
    for( int i=0; i<ts._len; i++ )
      for( int j=i+1; j<ts._len; j++ )
        if( ts._es[j].isa(ts._es[i]) ) { Type tmp = ts._es[i]; ts._es[i] = ts._es[j]; ts._es[j] = tmp; }
    return (ALL_TYPES = ts); // Preserve for tests
  }
  static void concat( Ary<Type> ts, Type[] ts1 ) {
    for( Type t1 : ts1 ) {
      assert !t1.above_center(); // Always below-center or equal, because we will dual anyways
      ts.push(t1);
      if( t1!=t1.dual() ) ts.push(t1.dual());
    }
  }

  static boolean check_startup() {
    int errs=0;
    Type[] ts = ALL_TYPES().asAry();

    // Confirm commutative & complete
    for( Type t0 : ts )
      for( Type t1 : ts ) {
        Type mt = t0.meet(t1);
        if( !t0.check_commute  (t1,mt) ) errs++;
        if( !t0.check_symmetric(t1,mt) ) errs++;
      }
    assert errs==0 : "Found "+errs+" symmetric errors";

    // Confirm associative
    for( Type t0 : ts )
      for( Type t1 : ts )
        for( Type t2 : ts ) {
          Type t01   = t0 .meet(t1 );
          Type t12   = t1 .meet(t2 );
          Type t01_2 = t01.meet(t2 );
          Type t0_12 = t0 .meet(t12);
          if( t01_2 != t0_12 && errs++ < 10 )
            System.err.println("("+t0+"&"+t1+") & "+t2+" == "+t0+" & ("+t1+" & "+t2+");\n"+
                               "("+t01      +") & "+t2+" == "+t0+" & ("+t12        +");\n"+
                               t01_2                  +" == "+t0_12);
        }
    assert errs==0 : "Found "+errs+" associative errors";


    // Confirm symmetry.  If A isa B, then A.join(C) isa B.join(C)
    for( Type t0 : ts )
      for( Type t1 : ts ) {
        if( t0.isa(t1) ) {
          for( Type t2 : ts ) {
            Type t02 = t0.join(t2);
            Type t12 = t1.join(t2);
            Type mt  = t02.meet(t12);
            if( mt != t12 && errs++ < 10 ) {
              System.err.println("("+t0+" ^ "+t2+") = "+t02+"; "+
                                 "("+t1+" ^ "+t2+") = "+t12+"; "+
                                 "their meet = "+mt+" which is not "+t12);
            }
          }
        }
      }
    assert errs==0 : "Found "+errs+" non-join-type errors";

    // Check scalar primitives; all are SCALARS and none sub-type each other.
    SCALAR_PRIMS = new Type[] { TypeInt.INT64, TypeFlt.FLT64, TypeMemPtr.ISUSED0, TypeFunPtr.GENERIC_FUNPTR, TypeRPC.ALL_CALL };
    for( Type t : SCALAR_PRIMS ) assert t.isa(TypeNil.SCALAR);
    for( int i=0; i<SCALAR_PRIMS.length; i++ )
      for( int j=i+1; j<SCALAR_PRIMS.length; j++ )
        assert !SCALAR_PRIMS[i].isa(SCALAR_PRIMS[j]);

    return true;
  }

  // True if value is above the centerline (no definite value, ambiguous)
  public boolean above_center() {
    return switch( _type ) {
      case TALL,  TCTRL -> false; // These are all below center
      case TANY, TXCTRL -> true ; // These are all above center
      default -> throw typerr(null);// Overridden in subclass
    };
  }
  // True if exactly a constant (not higher, not lower)
  public boolean is_con() {
    assert is_simple();
    return false;
  }

  // Return a long   from a TypeInt constant; assert otherwise.
  public long   getl() { throw typerr(null); }
  // Return a double from a TypeFlt constant; assert otherwise.
  public double getd() { throw typerr(null); }

  // "widen" a narrow type for primitive type-specialization and H-M
  // unification.  e.g. "3" becomes "int64".
  // TODO: This is NOT associative with MEET.
  // Example:
  //   5.widen.meet(2.3f) == nint64.meet(2.3f) == nScalar
  //   5.meet(2.3f).widen == nflt32.widen      == nflt64
  public Type widen() {
    return switch( _type ) {
    case TCTRL, TXCTRL -> Type.CTRL;
    case TANY, TALL -> this;
    case TMEMPTR, TMEM, TFUNPTR, TTUPLE, TSTRUCT -> this; // Do not touch
    default -> throw typerr(null); // Overridden in subclass
    };
  }

  // Sharpen pointer with memory
  public Type sharptr( Type ptr ) { return this==ANY ? TypeMem.ANYMEM.sharptr(ptr) : ptr; }

  // Make from existing type, replacing TMPs with alias from the map
  public Type make_from(Type head, TypeMem map, VBitSet visit) { return this; }

  static final VBitSet ARF = new VBitSet();
  public final BitsFun all_reaching_fidxs( TypeMem tmem) {
    assert ARF.isEmpty();
    BitsFun arf = _all_reaching_fidxs(tmem);
    ARF.clear();
    return arf;
  }
  BitsFun _all_reaching_fidxs( TypeMem tmem ) { return BitsFun.EMPTY; }
  // Recursion strings are always 2 chars, all upper-case
  private static boolean isRecur(String s) {
    return s.length()==2 && Character.isUpperCase(s.charAt(0)) && Character.isUpperCase(s.charAt(1));
  }

  // Parse an indented string to get a Type back.  Handles cyclic types (and
  // very inefficiently calls Cyclic.install many many times).
  // Example: "[0,ALL]{all,1 ->PA:*[0,5]@{^=any; n1=PA; v1=Scalar} }"
  static class Parse {
    final String _str;
    int _x;
    final NonBlockingHashMap<String,Type> _dups=new NonBlockingHashMap<>();
    Parse(String str) { _str = str; }
    Type type() { return type(null); }
    Type type(String cid) {
      return switch( skipWS() ) {
      case '*' -> cyc(TypeMemPtr.valueOf(this,cid));
      case '[' -> cyc(TypeFunPtr.valueOf(this,cid));
      case '(' -> cyc(TypeStruct.valueOf(this,cid,true ,false));
      case '@' -> cyc(TypeStruct.valueOf(this,cid,false,false));
      case '~' -> {
        if( at(_x+1)=='@' )
          { _x++; yield cyc(TypeStruct.valueOf(this,cid,false,true)); }
        yield simple_type(id());
      }
      case '0','1','2','3','4','5','6','7','8','9','-' -> {
        double d = num();
        Type t = ((long)d)==d ? TypeInt.con((long)d) : TypeFlt.con(d);
        if( cid!=null ) _dups.put(cid,t);
        yield t;
      }
      default -> {
        // Simple types or recursive type names
        String id = id();
        if( !peek(':') ) {      // Either a pre-defined name "FA" or a simple type "int64"
          Type t = _dups.get(id);
          if( t!=null ) { assert cid==null; yield t; } // Hit a pre-defined cyclic name
          t = simple_type(id); // Something like { int64, any, ~Scalar, nil }
          if( cid!=null ) _dups.put(cid,t);
          yield t;
        }
        assert cid==null;       // No doing things like "FA:XB:"
        // Lower case types are simple named types: "int:@{x=1}" or "Cat:@{legs=4}"
        if( !isRecur(id) ) {
          String tname = (id+':').intern();
          if( Util.eq(id,"int") || Util.eq(id,"flt"))
            yield TypeStruct.make(tname,type(null));
          yield ((TypeStruct)type(null)).set_name(tname);
        }

        RECURSIVE_MEET++;   // Ok, really start a recursive type
        Type t = type(id);
        if( --RECURSIVE_MEET == 0)
          t = Cyclic.install(t,_dups);
        yield t;
      }
      };
    }
    // Something like { int64, any, ~Scalar, nil }
    Type simple_type(String id) {
      // A simple type
      for( int i=0; i<STRS.length; i++ )
        if( Util.eq(id,STRS[i]) )
          return Type.make((byte)i);
      // Various names for integer and float
      Type t = TypeNil.valueOfNil(id);
      if( t!=null ) return t;
      t = TypeInt.valueOfInt(id);
      if( t!=null ) return t;
      t = TypeFlt.valueOfFlt(id);
      if( t!=null ) return t;
      throw unimpl();
    }
    <T extends Type> T cyc(T t) { return RECURSIVE_MEET==0 ? Cyclic.install(t,_dups) : t; }
    char at(int x) { return _str.charAt(x); }
    char skipWS() {
      while( !eos() && at(_x) <= ' ' ) _x++;
      return eos() ? (char)-1 : at(_x);
    }
    // If find 'c', advance cursor and true.
    boolean peek(char c) {
      if( skipWS()==c ) { _x++; return true; }
      else return false;
    }
    boolean eos() { return _x >= _str.length(); }
    // A number.  Either a pure integer, or contains a '.' and a double.
    // Possibly followed by a 'f' for a float.
    double num() {
      int i=0, d;
      int neg = peek('-') ? -1 : 1;
      while( !eos() &&  (d=at(_x)-'0') >= 0 && d<=9 )
        { i = i*10+d; _x++; }
      if( eos() || !peek('.') ) return i*neg; // Pure integer
      double dd = i, frac=10;
      while( !eos() &&  (d=at(_x)-'0') >= 0 && d<=9 )
        { dd += d/frac; frac *= 10; _x++; }
      if( peek('f') ) dd = (float)dd; // A float
      return dd*neg;                  // A double
    }
    // Skip whitespace and parse an identifier.
    String id() {
      skipWS();
      int oldx=_x;
      if( _x < _str.length() && isId0(at(_x)) ) _x++;
      while( _x < _str.length() && isId1(at(_x)) ) _x++;
      return _str.substring(oldx,_x).intern();
    }
    // Rules for an ID character
    private static boolean isId0(char c) {
      return c=='^' || c=='_' || c=='~' ||
        ('A' <= c && c <= 'Z') ||
        ('a' <= c && c <= 'z');
    }
    private static boolean isId1(char c) {
      return isId0(c) || 
        ('0' <= c && c <= '9') ||
        c=='*';
    }

    // Examples: [], [0], [5], [2,3,4], [0,ALL]
    <B extends Bits<B>> B bits( B b ) {
      require('[');
      if( peek(']') ) return b; // Empty
      do b = b.set(is_all() ? 1 : (int)num());
      while( peek(',') );
      require(']');
      return b;
    }
    private boolean is_all() { if( _str.startsWith("ALL", _x) ) { _x +=3; return true; } else return false; }
    // Demand
    void require(char c) {
      if( peek(c) ) return;
      System.err.println(_str);
      for( int i = 0; i< _x; i++ ) System.err.print(' ');
      System.err.println('^');
      System.err.println("Expected '"+c+"' but found '"+at(_x)+"', unable to parse a Type");
      throw unimpl();
    }
    @Override public String toString() { return _str.substring(_x); }
  }
  public static Type valueOf( String str ) { return str == null ? null : new Parse(str).type(); }

  RuntimeException typerr(Type t) {
    throw new RuntimeException("Should not reach here: internal type system error with "+this+(t==null?"":(" and "+t)));
  }
}
