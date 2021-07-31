package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;

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
// memory and named subtypes of the above.
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
// Named ints and flts "subtype", except for 0 which is canonically the same
// everywhere.  Example assuming a name "gal:flt32"
// ~flt64 -> ~flt32 -> gal:~flt32 -> {... gal:-pi, gal:-0.1, 0, gal:0.1, gal:pi, ... } -> gal:flt32 -> flt32 -> flt64
//
// OOPs are everywhere nullable; they always support a {oop+null, oop, null,
// oop&null} set of choices, where oop+null and oop&null are duals.
// Tuples are OOPS with an infinite list of values; the values are dualed
// structurally.
// Structs are tuples with a set of named fields; the fields can be top, a
// field name, or bottom.
// Strings are OOPs which again can be top, a constant, or bottom.
//
// Because the meet is commutative, associative, distributive, the following holds:
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

// Current solution is that nil is signed: XNIL and NIL.

public class Type<T extends Type<T>> implements Cloneable {
  static private int CNT=1;
  public int _uid;   // Unique ID, will have gaps, used to uniquely order Types
  public int _hash;      // Hash for this Type; built recursively
  byte _type;            // Simple types use a simple enum
  public String _name;   // All types can be named
  T _dual; // All types support a dual notion, eagerly computed and cached here

  protected Type() { _uid = _uid(); }
  private int _uid() { return CNT++; }
  @SuppressWarnings("unchecked")
  protected T init(byte type, String name) { _type=type; _name=name; return (T)this; }
  @Override public final int hashCode( ) { assert _hash!=0; return _hash; }
  // Compute the hash and return it, with all child types already having their
  // hash computed.  Subclasses override this.
  int compute_hash() { return (_type<<1)|1|_name.hashCode(); }

  // Is anything equals to this?
  @Override public boolean equals( Object o ) {
    if( this == o ) return true;
    if( !(o instanceof Type) ) return false;
    Type t = (Type)o;
    return _type==t._type && Util.eq(_name,t._name);
  }
  public boolean cycle_equals( Type t ) {
    assert is_simple();         // Overridden in subclasses
    return _type==t._type && Util.eq(_name,t._name);
  }

  // In order to handle recursive printing, this is the only toString call in
  // the Type hierarchy.  Instead, subtypes override 'str(...)' where the extra
  // args stop cycles (VBitSet) or sharpen pointers (TypeMem), or optimize
  // printing strings (SB).
  @Override public final String toString() { return str(new SB(),new VBitSet(),null,true).toString(); }
  // Nice, REPL-friendly and error-friendly dump.
  // Debug flag dumps, e.g. raw aliases and raw fidxs.
  // This is the 'base' printer, as changing this changes behavior.
  public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) { return sb.p(_name).p(STRS[_type]); }

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

  // Object Pooling to handle frequent (re)construction of temp objects being
  // interned.  One-entry pool for now.
  private static Type FREE=null;
  private T free( T ret ) { FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  private static Type make( byte type ) {
    Type t1 = FREE == null ? new Type() : FREE;
    FREE = null;
    Type t2 = t1.init(type,"").hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  // Hash-Cons - all Types are interned in this hash table.  Thus an equality
  // check of a (possibly very large) Type is always a simple pointer-equality
  // check, except during construction and intern'ing.
  private static final ConcurrentHashMap<Type,Type> INTERN = new ConcurrentHashMap<>();
  public static int RECURSIVE_MEET;    // Count of recursive meet depth
  @SuppressWarnings("unchecked")
  final T hashcons() {
    _hash = compute_hash();     // Set hash
    T t2 = (T)INTERN.get(this); // Lookup
    if( t2!=null ) {            // Found prior
      assert t2._dual != null;  // Prior is complete with dual
      assert this != t2;        // Do not hashcons twice, should not get self back
      return t2;                // Return prior
    }
    if( RECURSIVE_MEET > 0 )    // Mid-building recursive types; do not intern
      return (T)this;
    // Not in type table
    _dual = null;                // No dual yet
    INTERN.put(this,this);       // Put in table without dual
    T d = xdual();               // Compute dual without requiring table lookup, and not setting name
    d._name = _name;             // xdual does not set name either
    d._hash = d.compute_hash();  // Set dual hash
    _dual = d;
    if( this==d ) return d;      // Self-symmetric?  Dual is self
    assert !equals(d);           // Self-symmetric is handled by caller
    assert d._dual==null;        // Else dual-dual not computed yet
    assert INTERN.get(d)==null;
    d._dual = (T)this;
    INTERN.put(d,d);
    return (T)this;
  }
  // Remove a forward-ref type from the interning dictionary, prior to
  // interning it again - as a self-recursive type
  @SuppressWarnings("unchecked")
  final T untern( ) {
    assert _hash != 0;
    assert INTERN.get(this)==this;
    Type rez = INTERN.remove(this);
    assert rez == this;
    return (T)this;
  }
  @SuppressWarnings("unchecked")
  final T retern( ) {
    assert _dual._dual == this;
    assert _hash != 0;
    assert INTERN.get(this)==null;
    INTERN.put(this,this);
    assert INTERN.get(this)==this;
    return (T)this;
  }
  boolean interned() { return INTERN.get(this)==this; }
  Type intern_lookup() { return INTERN.get(this); }
  static int intern_size() { return INTERN.size(); }
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
    if( this != v || _dual==null || _dual._dual!=this || compute_hash()!=_hash ) return false;
    switch( _type ) {
    case TSTRUCT:
      TypeStruct ts = (TypeStruct)this;
      for( TypeFld fld : ts._flds )
        if( INTERN.get(fld)==null )
          return false;
      break;
    case TMEMPTR:
      TypeMemPtr tmp = (TypeMemPtr)this;
      if( INTERN.get(tmp._obj)==null )
        return false;
      break;
    case TFLD:
      TypeFld fld = (TypeFld)this;
      if( INTERN.get(fld._t)==null )
        return false;
      break;
    default: break;
    }
    return true;
  }
  // Debugging helper
  static Type intern_find(int uid) {
    for( Type k : INTERN.keySet() )
      if( k._uid==uid )
        return k;
    return null;
  }

  // Simple types are implemented fully here.  "Simple" means: the code and
  // type hierarchy are simple, not that the Type is conceptually simple.
  static final byte TALL    = 0; // Bottom
  static final byte TANY    = 1; // Top
  static final byte TCTRL   = 2; // Ctrl flow bottom
  static final byte TXCTRL  = 3; // Ctrl flow top (mini-lattice: any-xctrl-ctrl-all)
  // Scalars; all possible finite types that fit in a machine register;
  // includes pointers (functions, structs), ints, floats; excludes state of
  // Memory and Ctrl.  Scalars are stateless and "free" to make copies.
  static final byte TSCALAR = 4; // Scalars
  static final byte TXSCALAR= 5; // Invert scalars
  // Not-nil Scalars.  Same as Scalars above but excludes nil/0.  Note that I
  // have a doubly represented type: TypeNil.make(SCALAR) would add a nil to a
  // SCALAR except SCALAR already has a nil.  This means if I define SCALAR as
  // not having a nil, I could drop TNSCALR and TXNSCALR... but that makes
  // TypeNil.make(SCALAR) below SCALAR in the lattice, which gets ugly.
  static final byte TNSCALR = 6; // Scalars-not-nil
  static final byte TXNSCALR= 7; // Invert Scalars-not-nil
  static final byte TREAL   = 8; // All Real Numbers
  static final byte TXREAL  = 9; // Any Real Numbers; dual of REAL
  static final byte TNREAL  =10; // Numbers-not-nil
  static final byte TXNREAL =11; // Invert Numbers-not-nil
  static final byte TNIL    =12; // The Nil-type
  static final byte TXNIL   =13; // NIL.dual
  static final byte TSIMPLE =14; // End of the Simple Types
  private static final String[] STRS = new String[]{"all","any","Ctrl","~Ctrl","Scalar","~Scalar","nScalar","~nScalar","Real","~Real","nReal","~nReal","nil","0"};
  static final byte TINT    =15; // All Integers, including signed/unsigned and various sizes; see TypeInt
  static final byte TFLT    =16; // All IEEE754 Float Numbers; 32- & 64-bit, and constants and duals; see TypeFlt
  static final byte TRPC    =17; // Return PCs; Continuations; call-site return points; see TypeRPC
  static final byte TTUPLE  =18; // Tuples; finite collections of unrelated Types, kept in parallel
  static final byte TOBJ    =19; // Memory objects; arrays and structs and strings
  static final byte TSTRUCT =20; // Memory Structs; tuples with named fields
  static final byte TARY    =21; // Memory Array type
  static final byte TSTR    =22; // Memory String type; an array of chars
  static final byte TFLD    =23; // Fields in structs
  static final byte TMEM    =24; // Memory type; a map of Alias#s to TOBJs
  static final byte TMEMPTR =25; // Memory pointer type; a collection of Alias#s
  static final byte TFUNPTR =26; // Function pointer, refers to a collection of concrete functions
  static final byte TFUNSIG =27; // Function signature; formals & ret.  Not any concrete function.
  static final byte TLIVE   =28; // Liveness; backwards flow of TypeObj
  static final byte TLAST   =29; // Type check

  public  static final Type ALL    = make( TALL   ); // Bottom
  public  static final Type ANY    = make( TANY   ); // Top
  public  static final Type CTRL   = make( TCTRL  ); // Ctrl
  public  static final Type XCTRL  = make(TXCTRL  ); // Ctrl
  public  static final Type  SCALAR= make( TSCALAR); // ptrs, ints, flts; things that fit in a machine register
  public  static final Type XSCALAR= make(TXSCALAR); // ptrs, ints, flts; things that fit in a machine register
  public  static final Type  NSCALR= make( TNSCALR); // Scalars-not-nil
  public  static final Type XNSCALR= make(TXNSCALR); // Scalars-not-nil
  public  static final Type   NIL  = make( TNIL   ); // The Nil.
  public  static final Type  XNIL  = make(TXNIL   ); // The ~Nil.
  public  static final Type   REAL = make( TREAL  );
  private static final Type  XREAL = make(TXREAL  );
          static final Type  NREAL = make( TNREAL );
  private static final Type XNREAL = make(TXNREAL );

  // Collection of sample types for checking type lattice properties.
  private static final Type[] TYPES = new Type[]{ALL,CTRL,SCALAR,NSCALR,REAL,NREAL};

  // The complete list of primitive types that are disjoint and also is-a
  // SCALAR; nothing else is a SCALAR except what is on this list (or
  // subtypes).  Useful when type-specializing functions to break SCALAR args
  // into a concrete list of specific types.  Specifically excludes e.g.
  // TypeTuple - these may be passed as a scalar reference type in the future
  // but for now Tuples explicitly refer to multiple values, and a SCALAR is
  // exactly 1 value.
  private static /*final*/ Type[] SCALAR_PRIMS;

  private boolean is_simple() { return _type < TSIMPLE; }
  private boolean is_ptr() { byte t = _type;  return t == TFUNPTR || t == TMEMPTR; }
  private boolean is_num() { byte t = _type;  return t == TREAL || t == TXREAL || t == TNREAL || t == TXNREAL || t == TINT || t == TFLT; }
  // True if 'this' isa SCALAR, without the cost of a full 'meet()'
  private static final byte[] ISA_SCALAR = new byte[]{/*ALL-0*/0,0,0,0,1,1,1,1,1,1,/*TNREAL-10*/1,1,1,1,/*TSIMPLE-14*/0, 1,1,1,0,0,0,0,0,0,0,1,1,/*TFUNSIG-27*/0,/*TLIVE-28*/0}/*TLAST=29*/;
  public final boolean isa_scalar() { assert ISA_SCALAR.length==TLAST; return ISA_SCALAR[_type]!=0; }
  // Simplify pointers (lose what they point at).
  public Type simple_ptr() { return this; }

  // Return cached dual
  public final T dual() { return _dual; }

  // Compute dual right now.  Overridden in subclasses.
  @SuppressWarnings("unchecked")
  T xdual() { return (T)new Type().init((byte)(_type^1),""); }
  T rdual() { assert _dual!=null; return _dual; }

  // Memoize meet results
  private static class Key {
    static Key K = new Key(null,null);
    static NonBlockingHashMap<Key,Type> INTERN_MEET = new NonBlockingHashMap<>();
    Key(Type a, Type b) { _a=a; _b=b; }
    Type _a, _b;
    @Override public int hashCode() { return ((_a._hash<<17)|(_a._hash>>>15))^_b._hash; }
    @Override public boolean equals(Object o) { return _a==((Key)o)._a && _b==((Key)o)._b; }
    static Type get(Type a, Type b) {
      K._a=a;
      K._b=b;
      return INTERN_MEET.get(K);
    }
    static void put(Type a, Type b, Type mt) {
      INTERN_MEET.put(new Key(a,b),mt);
      // Uncomment to check hash quality.
      //Util.hash_quality_check_per(INTERN_MEET);
    }
    static void intern_meet_quality_check() {
      NonBlockingHashMapLong<Integer> hashs = new NonBlockingHashMapLong<>();
      for( Key k : INTERN_MEET.keySet() ) {
        int hash = k.hashCode();
        Integer ii = hashs.get(hash);
        hashs.put(hash,ii==null ? 1 : ii+1);
      }
      int[] hist = new int[16];
      int maxval=0;
      long maxkey=-1;
      for( long l : hashs.keySet() ) {
        int reps = hashs.get(l);
        if( reps > maxval ) { maxval=reps; maxkey=l; }
        if( reps < hist.length ) hist[reps]++;
        else System.out.println("hash "+l+" repeats "+reps);
      }
      for( int i=0; i<hist.length; i++ )
        if( hist[i] > 0 )
          System.out.println("Number of hashes with "+i+" repeats: "+hist[i]);
      System.out.println("Max repeat key "+maxkey+" repeats: "+maxval);
    }

  }

  // Compute the meet
  public final Type meet( Type t ) {
    // Short cut for the self case
    if( t == this ) return this;
    // Short-cut for seeing this meet before
    Type mt = Key.get(this,t);
    if( mt != null ) return mt;

    // "Triangulate" the matrix and cut in half the number of cases.
    // Reverse; xmeet 2nd arg is never "is_simple" and never equal to "this".
    // This meet ignores the _name field, and can return any-old name it wants.
    mt = !is_simple() && t.is_simple() ? t.xmeet(this) : xmeet(t);

    // Meet the names.  Subclasses basically ignore the names as they have
    // their own complicated meets to perform, so we meet them here for all.
    Type nmt = xmt_name(t,mt);

    // Quick check on NIL: if either argument is NIL the result is allowed to
    // be NIL...  but nobody in the lattice can make a NIL from whole cloth, or
    // we get the crossing-nil bug.
    assert (nmt != NIL && nmt!=XNIL) || this==NIL || this==XNIL || t==NIL || t==XNIL;

    // Record this meet, to short-cut next time
    if( RECURSIVE_MEET == 0 )   // Only not mid-building recursive types;
      Key.put(this,t,nmt);
    return nmt;
  }

  // Meet the names.  Subclasses basically ignore the names as they have
  // their own complicated meets to perform, so we meet them here for all.
  private Type xmt_name(Type t, Type mt) {
    String n = mtname(t,mt);    // Meet name strings
    // If the names are incompatible and the meet remained high then the
    // mismatched names force a drop.
    if( n.length() < _name.length() && n.length() < t._name.length() && mt.above_center() ) {
      if( mt.interned() ) // recursive type creation?
        mt = mt.dual();   // Force low
    }
    if( mt.is_simple() ) n=""; // No named simple types
    if( mt._type==TOBJ ) n=""; // OBJ splits into strings (arrays) and structs, which can keep their names

    // Inject the name
    if( !Util.eq(mt._name,n) )  // Fast path cutout
      mt = mt.set_name(n);
    return mt;
  }

  // Compute meet right now.  Overridden in subclasses.
  // Handles cases where 'this.is_simple()' and unequal to 't'.
  // Subclassed xmeet calls can assert that '!t.is_simple()'.
  protected Type xmeet(Type t) {
    assert is_simple(); // Should be overridden in subclass
    // ANY meet anything is thing; thing meet ALL is ALL
    if( _type==TALL || t._type==TANY ) return this;
    if( _type==TANY || t._type==TALL ) return    t;

    // Ctrl can only meet Ctrl, XCtrl or Top
    byte type = (byte)(_type|t._type); // the OR is low if both are low
    if(  type <= TXCTRL ) return _type==TXCTRL && t._type==TXCTRL ? XCTRL : CTRL;
    if( _type <= TXCTRL || t._type <= TXCTRL ) return ALL;

    // Meeting scalar and non-scalar falls to ALL.  Includes most Memory shapes.
    if( isa_scalar() ^ t.isa_scalar() ) return ALL;

    // Memory does something complex with memory
    if( t._type==TMEM ) return t.xmeet(this);

    // Scalar is close to bottom: nearly everything falls to SCALAR, except
    // Bottom (already handled) and Control (error; already handled).
    if( _type == TSCALAR || t._type == TSCALAR ) return SCALAR;

    // ~Scalar is close to Top: it falls to nearly anything.
    if(   _type == TXSCALAR ) return t   ;
    if( t._type == TXSCALAR ) return this;

    // Not-nil variants
    if(   _type == TNSCALR ) return t.must_nil() ? SCALAR : NSCALR;
    if( t._type == TNSCALR ) return   must_nil() ? SCALAR : NSCALR;
    if(   _type == TXNSCALR) return t.not_nil();
    if( t._type == TXNSCALR) return   not_nil();

    if( _type == TNIL || _type == TXNIL ) return t.meet_nil(this);

    // Scalar values break out into: nums(reals (int,flt)), GC-ptrs (structs(tuples), arrays(strings)), fun-ptrs, RPC
    if( t._type == TFUNPTR ||
        t._type == TMEMPTR ||
        t._type == TRPC   )
      return cross_nil(t);

    boolean that_oop = t.is_ptr();
    boolean that_num = t.is_num();
    assert !(that_oop&&that_num);

    // Down to just nums and GC-ptrs
    if( is_num() ) {
      // May be OOP0 or STR or STRUCT or TUPLE
      if( that_oop ) return (must_nil() || t.must_nil()) ? SCALAR : NSCALR;
      if( that_num || t==NIL || t==XNIL ) {
        // Real; same pattern as ANY/ALL, or SCALAR/XSCALAR
        if( _type == TREAL || t._type == TREAL ) return REAL;
        if(   _type == TXREAL ) return t   ;
        if( t._type == TXREAL ) return this;

        // Not-nil variants
        if(   _type == TNREAL ) return t.must_nil() ? REAL : NREAL;
        if( t._type == TNREAL ) return   must_nil() ? REAL : NREAL;
        if(   _type == TXNREAL) return t.not_nil();
        if( t._type == TXNREAL) return   not_nil();
      }
    }
    throw typerr(t);
  }

  // Named types are essentially a subclass of any type.
  // Examples:
  //   B:A:int << B:int << int   // Subtypes
  //     B:int.isa (int)
  //   B:A:int.isa (B:int)
  //     C:int.meet(B:int) == int
  //   B:A:int.meet(C:int) == int
  //
  //   B:A:~int.join(B:~int) == B:A:~int
  //     C:~int.join(B:~int) ==     ~int
  //
  //   B: int.meet(  ~int) == B:   int.meet(B:~int) == B:int
  //   B:~int.meet(   int) ==      int
  //   B:~int.meet(C: int) ==      int
  //   B:~int.meet(B: int) == B:   int
  //   B:~int.meet(C:~int) ==      int // Nothing in common, fall to int
  //   B:~int.meet(  ~int) == B:  ~int
  // B:A:~int.meet(B:~int) == B:A:~int // both high, keep long; short guy high, keep long
  // B:A:~int.meet(B: int) == B:   int // one low, keep low   ; short guy  low, keep short
  // B:A: int.meet(B:~int) == B:A: int // one low, keep low   ; short guy high, keep long
  // B:A: int.meet(B: int) == B:   int // both low, keep short; short guy  low, keep short
  //
  // B:A:~int.meet(B:D:~int) == B:int // Nothing in common, fall to int

  static boolean check_name( String n ) { return n.isEmpty() || n.charAt(n.length()-1)==':'; }
    // Make a named variant of any type, by just adding a name.
  @SuppressWarnings("unchecked")
  public final T set_name(String name) {
    assert check_name(name);
    Type t1 = clone();
    t1._name = name;
    Type t2 = t1.hashcons();
    return (T)(t1==t2 ? t1 : t1.free(t2));
  }
  public boolean has_name() { return !_name.isEmpty(); }
  @SuppressWarnings("unchecked")
  public final T remove_name() { // TODO: remove 1 layer of names
    if( !has_name() ) return (T)this;
    Type t1 = clone();
    t1._name = "";
    Type t2 = t1.hashcons();
    return (T)(t1==t2 ? t1 : t1.free(t2));
  }

  // TODO: will also need a unique lexical numbering, not just a name, to
  // handle the case of the same name used in two different scopes.
  final String mtname(Type t, Type mt) {
    Type   t0 = this,  t1 = t;
    String s0 = t0._name, s1 = t1._name;
    assert check_name(s0) && check_name(s1);
    if( Util.eq(s0,s1) ) return s0;
    // Sort by name length
    if( s0.length() > s1.length() ) { t1=this; t0=t; s0=t0._name; s1=t1._name; }
    int x = 0, i;  char c;    // Last colon separator index
    // Find split point
    for( i = 0; i < s0.length(); i++ ) {
      if( (c=s0.charAt(i)) != s1.charAt(i) )
        break;
      if( c==':' ) x=i;
    }
    // If s0 is a prefix of s1, and s0 is high then it can cover s1.
    if( i==s0.length() && t0.above_center() && (!t1.above_center() || mt.above_center()) )
      return s1;
    // Keep the common prefix, which might be all of s0
    String s2 = i==s0.length() ? s0 : s0.substring(0, x).intern();
    assert check_name(s2);
    return s2;
  }

  // By design in meet, args are already flipped to order _type, which forces
  // symmetry for things with badly ordered _type fields.  The question is
  // still interesting for other orders.
  private boolean check_commute( Type t, Type mt ) {
    if( t==this ) return true;
    if( is_simple() && !t.is_simple() ) return true; // By design, flipped the only allowed order
    Type mt2 = t.xmeet(this);   // Reverse args and try again

    // Also reverse names.
    Type nmt2 = t.xmt_name(this,mt2);

    if( mt==nmt2 ) return true;
    System.out.println("Meet not commutative: "+this+".meet("+t+")="+mt+",\n but "+t+".meet("+this+")="+nmt2);
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
  // E.g. ANY-isa-XSCALAR; XSCALAR-isa-XREAL; XREAL-isa-Int(Any); Int(Any)-isa-Int(3)
  public boolean isa( Type t ) { return meet(t)==t; }
  // True if 'this' isa 't' but is not equal to 't'
  public boolean above( Type t ) { return t != this && meet(t)==t; }

  // MEET at a Loop; optimize no-final-updates on backedges.
  public Type meet_loop(Type t2) { return meet(t2); }


  // Report OOB based on shallowest OOB component.
  public Type oob_deep( Type t ) { return oop_deep_impl(t); }
  // Report OOB based on shallowest OOB component.
  public Type oop_deep_impl(Type t) { return oob(); }
  public Type       oob( ) { return oob(ALL); }
  public Type       oob(Type       e) { return above_center() ? e.dual() : e; }
  public TypeObj    oob(TypeObj    e) { return above_center() ? (TypeObj)e.dual() : e; }
  public TypeStruct oob(TypeStruct e) { return above_center() ? e.dual() : e; }
  public TypeMem    oob(TypeMem    e) { return above_center() ? e.dual() : e; }
  public TypeMemPtr oob(TypeMemPtr e) { return above_center() ? e.dual() : e; }

  public static void init0( HashMap<String,Type> types ) {
    types.put("real",REAL);
    types.put("scalar",SCALAR);
    TypeInt.init1(types);
    TypeFlt.init1(types);
    TypeStr.init1(types);
  }

  private static Ary<Type> ALL_TYPES; // Used for tests
  public static Ary<Type> ALL_TYPES() {
    if( ALL_TYPES != null ) return ALL_TYPES;
    Ary<Type> ts = new Ary<>(new Type[1],0);
    concat(ts,Type      .TYPES);
    concat(ts,TypeFlt   .TYPES);
    concat(ts,TypeFunPtr.TYPES);
    concat(ts,TypeFunSig.TYPES);
    concat(ts,TypeInt   .TYPES);
    concat(ts,TypeLive  .TYPES);
    concat(ts,TypeMem   .TYPES);
    concat(ts,TypeMemPtr.TYPES);
    concat(ts,TypeObj   .TYPES);
    concat(ts,TypeRPC   .TYPES);
    concat(ts,TypeStr   .TYPES);
    concat(ts,TypeStruct.TYPES);
    concat(ts,TypeTuple .TYPES);
    concat(ts,TypeAry   .TYPES);
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
      assert !t1.above_center(); // Always below-center or equal, because we'll dual anyways
      ts.push(t1);
      if( t1!=t1.dual() ) ts.push(t1.dual());
    }
  }

  static boolean check_startup() {
    Type[] ts = ALL_TYPES().asAry();

    // Confirm commutative & complete
    for( Type t0 : ts )
      for( Type t1 : ts ) {
        Type mt = t0.meet(t1);
        assert t0.check_commute  (t1,mt);
        assert t0.check_symmetric(t1,mt);
      }

    // Confirm associative
    int errs=0;
    for( Type t0 : ts )
      for( Type t1 : ts )
        for( Type t2 : ts ) {
          Type t01   = t0 .meet(t1 );
          Type t12   = t1 .meet(t2 );
          Type t01_2 = t01.meet(t2 );
          Type t0_12 = t0 .meet(t12);
          if( t01_2 != t0_12 && errs++ < 10 )
            System.err.println("("+t0+"&"+t1+") & "+t2+" == "+t0+" & ("+t1+" & "+t2+"); "+
                               "("+t01      +") & "+t2+" == "+t0+" & ("+t12        +"); "+
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
    SCALAR_PRIMS = new Type[] { TypeInt.INT64, TypeFlt.FLT64, TypeMemPtr.OOP0, TypeFunPtr.GENERIC_FUNPTR, TypeRPC.ALL_CALL };
    for( Type t : SCALAR_PRIMS ) assert t.isa(SCALAR);
    for( int i=0; i<SCALAR_PRIMS.length; i++ )
      for( int j=i+1; j<SCALAR_PRIMS.length; j++ )
        assert !SCALAR_PRIMS[i].isa(SCALAR_PRIMS[j]);

    return true;
  }

  // True if value is above the centerline (no definite value, ambiguous)
  public boolean above_center() {
    switch( _type ) {
    case TALL:
    case TCTRL:
    case TREAL:   case TNREAL:
    case TSCALAR: case TNSCALR:
    case TNIL:
      return false;             // These are all below center
    case TANY:
    case TXCTRL:
    case TXREAL:   case TXNREAL:
    case TXSCALAR: case TXNSCALR:
    case TXNIL:
      return true;              // These are all above center
    default: throw typerr(null);// Overridden in subclass
    }
  }
  // True if value is higher-equal to SOME constant.
  public boolean may_be_con() {
    switch( _type ) {
    case TALL:
    case TSCALAR:  case TNSCALR:
    case TREAL:    case TNREAL:
    case TXCTRL:
    case TCTRL:
      return false;             // These all include not-constant things
    case TANY:
    case TXREAL:   case TXNREAL:
    case TXSCALAR: case TXNSCALR:
    case TNIL:     case TXNIL:
      return true;              // These all include some constants
    default: throw typerr(null);
    }
  }
  // True if exactly a constant (not higher, not lower)
  public boolean is_con() {
    switch( _type ) {
    case TALL:
    case TCTRL:
    case TNREAL:
    case TREAL:
    case TNSCALR:
    case TSCALAR:
    case TANY:
    case TXCTRL:
    case TXNREAL:
    case TXREAL:
    case TXNSCALR:
    case TXSCALAR:
      return false;             // Not exactly a constant
    case TNIL: case TXNIL:
      return true;
    default: throw typerr(null);// Overridden in subclass
    }
  }
  public Type high() { return above_center() ? this : dual(); }

  // Return true if this is a forward-ref function pointer (return type from EpilogNode)
  public boolean is_forward_ref() { return false; }

  // Return a long   from a TypeInt constant; assert otherwise.
  public long   getl() { if( _type==TNIL || _type==TXNIL ) return 0; throw typerr(null); }
  // Return a double from a TypeFlt constant; assert otherwise.
  public double getd() { if( _type==TNIL || _type==TXNIL ) return 0.0; throw typerr(null); }
  // Return a String from a TypeStr constant; assert otherwise.
  public String getstr() { throw typerr(null); }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  public byte isBitShape(Type t) {
    if( has_name() || t.has_name() ) throw com.cliffc.aa.AA.unimpl();
    if( _type == TNIL || _type==TXNIL ) return 0; // Nil is free to convert always
    if( above_center() && isa(t) ) return 0; // Can choose compatible format
    if( _type == t._type ) return 0; // Same type is OK
    if( t._type==TSCALAR ) return 0; // Generic function arg never requires a conversion
    if( _type == TALL || _type == TSCALAR || _type == TNSCALR ) return -1; // Scalar has to resolve
    if( (_type == TREAL || _type == TNREAL) && t.is_num() ) return -1; // Real->Int/Flt has to resolve
    if( t._type == TNIL || t._type == TXNIL ) return (byte)(may_nil() ? -1 : 99); // Must resolve to a NIL first

    throw typerr(t);  // Overridden in subtypes
  }
  // "widen" a narrow type for primitive type-specialization and H-M
  // unification.  e.g. "3" becomes "int64".
  public Type widen() {
    switch( _type ) {
    case TREAL:   case TXREAL:
    case TSCALAR: case TXSCALAR:
    case TNSCALR: case TXNSCALR:
    case TNIL:    case TXNIL:
      return SCALAR;
    case TANY : case TALL  :
      return this;
    case TCTRL: case TXCTRL:
      return Type.CTRL;
    default: throw typerr(null); // Overridden in subclass
    }
  }

  // True if type must include a nil (as opposed to may-nil, which means the
  // type can choose something other than nil).
  public boolean must_nil() {
    switch( _type ) {
    case TALL:
    case TREAL:
    case TSCALAR:
    case TNIL: case TXNIL:
    case TCTRL:  // Nonsense, only for IfNode.value test
    case TXCTRL: // Nonsense, only for IfNode.value test
    case TMEM:   // Nonsense, only for IfNode.value test
      return true;              // These all must include a nil
    case TANY:                  // All above-center types are not required to include a nil
    case TXREAL:
    case TXSCALAR:
    case TXNSCALR: case TNSCALR:
    case TXNREAL:  case TNREAL:
      return false;             // These all may be non-nil
    default: throw typerr(null); // Overridden in subclass
    }
  }
  // Mismatched scalar types that can only cross-nils
  final Type cross_nil(Type t) { return must_nil() || t.must_nil() ? SCALAR : NSCALR; }

  // True if type may include a nil (as opposed to must-nil).
  // True for many above-center or zero values.
  public boolean may_nil() {
    switch(_type) {
    case TALL:
    case TREAL:
    case TSCALAR:
    case TXNSCALR: case TNSCALR:
    case TXNREAL:  case TNREAL:
    case TTUPLE:
      return false;
    case TANY:
    case TXREAL:
    case TXSCALAR:
    case TCTRL:  // Nonsense, only for IfNode.value test
    case TXCTRL: // Nonsense, only for IfNode.value test
    case TMEM:   // Nonsense, only for IfNode.value test
      return true;
    default: throw typerr(null); // Overridden in subclass
    }
  }

  // Return the type without a nil-choice.  Only applies to above_center types,
  // as these are the only types with a nil-choice.  Only called during meets
  // with above-center types.  If called with below-center, there is no
  // nil-choice (might be a must-nil but not a choice-nil), so can return this.
  Type not_nil() {
    switch( _type ) {
    case TXSCALAR:  return XNSCALR;
    case TXREAL  :  return XNREAL ;
    case TSCALAR:   case TNSCALR:   case TXNSCALR:
    case TREAL:     case TNREAL:    case TXNREAL:
    case TNIL:      case TXNIL:
      return this;
    default: throw typerr(null); // Overridden in subclass
    }
  }
  public Type meet_nil(Type nil) {
    assert nil==NIL || nil==XNIL;
    switch( _type ) {
    case TANY:
    case TXREAL:
    case TXSCALAR:
    case TXNIL:   return nil; // Preserve high/low flavor
    case TNIL:    return NIL;
    case TXNREAL:
    case TXNSCALR:  return TypeInt.BOOL;
    case TREAL:   case TNREAL:    return REAL;
    case TSCALAR: case TNSCALR:   return SCALAR;
    case TCTRL:   case TXCTRL:
    case TOBJ:
    case TSTR:
    case TSTRUCT:
    case TMEM:      return ALL;
    default:        throw typerr(null); // Overridden in subclass
    }
  }

  // Is t type contained within this?  Short-circuits on a true
  public final boolean contains( Type t ) { return contains(t,null); }
  boolean contains( Type t, VBitSet bs ) { return this==t; }

  // Sharpen pointer with memory
  public Type sharptr( Type ptr ) { return this==ANY ? TypeMem.ANYMEM.sharptr(ptr) : ptr; }

  // Apply the test(); if it returns true iterate over all nested child types.
  // If the test returns false, short-circuit the walk.  No attempt to guard
  // against recursive structure walks, so the 'test' must return false when
  // visiting the same Type again.
  void walk( Predicate<Type> p ) { assert is_simple(); p.test(this); }

  TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) { return null; }

  // Display might be Scalar or ~Scalar at GVN start
  public boolean is_display_ptr() { return _type==TSCALAR || _type==TXSCALAR || _type==TNIL || _type==TXNIL || _type==TANY || _type==TALL; }
  boolean is_display() { return false; }

  RuntimeException typerr(Type t) {
    throw new RuntimeException("Should not reach here: internal type system error with "+this+(t==null?"":(" and "+t)));
  }
  @SuppressWarnings("unchecked")
  protected Type clone() {
    try {
      Type t = (Type)super.clone();
      t._uid = _uid();
      t._dual = null;
      t._hash = 0;
      if( t instanceof TypeStruct )
        ((TypeStruct)t)._cyclic = false;
      return t;
    }
    catch( CloneNotSupportedException cns ) { throw new RuntimeException(cns); }
  }
}
