package com.cliffc.aa.type;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.function.Consumer;
import java.util.function.Predicate;

/** an implementation of language AA
 */

// C2-style type system, with Meet & Dual.  This is a distributed complete
// bounded lattice.  See https://en.wikipedia.org/wiki/Complete_lattice.

// Symmetric around the centerline of constants.  Fixed height, so a finite
// count of Meet stablizes; a unique All (Bottom; no known value) and due to
// symmetry a unique Any (Top, all values simultaneously).  Support function
// types, various kinds of numeric ranges, nil, tuples and structs, and named
// subtypes of the above.
//
// During program typing, always keeping the "loosest" possible program and if
// this program still types as 'Any' then the program is ambiguious.  'All'
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
public class Type<T extends Type<T>> {
  static private int CNT=1;
  final int _uid=CNT++;  // Unique ID, will have gaps, used to uniquely order Types in Unions
  public int _hash;      // Hash for this Type; built recursively
  byte _type;            // Simple types use a simple enum
  boolean _cyclic;       // Part of a type cycle
  T _dual;  // All types support a dual notion, lazily computed and cached here

  protected Type(byte type) { init(type); }
  protected void init(byte type) { _type=type; _cyclic=false; }
  @Override public final int hashCode( ) { return _hash; }
  // Compute the hash and return it, with all child types already having their
  // hash computed.  Subclasses override this.
  int compute_hash() { assert is_simple(); return _type; }

  // Is anything equals to this?
  @Override public boolean equals( Object o ) {
    assert is_simple();         // Overridden in subclasses
    if( this == o ) return true;
    return (o instanceof Type) && _type==((Type)o)._type;
  }
  public boolean cycle_equals( Type o ) {
    assert is_simple();         // Overridden in subclasses
    return _type==o._type;
  }

  // In order to handle recursive printing, this is the only toString call in
  // the Type hierarchy.  Instead, subtypes override 'str(HashSet)' where the
  // HashSet is only installed by the head of a type-cycle (always and only
  // TypeName) and is used (again only by TypeName) to end cyclic printing.
  // All other 'str()' callers just pass along.
  @Override public final String toString() { return str(null); }
  String str( BitSet dups ) { return STRS[_type]; }

  // Object Pooling to handle frequent (re)construction of temp objects being
  // interned.  One-entry pool for now.
  private static Type FREE=null;
  protected T free( T ret ) { assert getClass()==Type.class; FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  private static Type make( byte type ) {
    Type t1 = FREE;
    if( t1 == null ) t1 = new Type(type);
    else { FREE = null; t1.init(type); }
    Type t2 = t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  // Hash-Cons - all Types are interned in this hash table.  Thus an equality
  // check of a (possibly very large) Type is always a simple pointer-equality
  // check, except during construction and intern'ing.
  private static ConcurrentMap<Type,Type> INTERN = new ConcurrentHashMap<>();
  static int RECURSIVE_MEET;    // Count of recursive meet depth
  @SuppressWarnings("unchecked")
  final Type hashcons() {
    _hash = compute_hash();     // Set hash
    Type t2 = INTERN.get(this); // Lookup
    if( t2!=null ) {            // Found prior
      assert t2._dual != null;  // Prior is complete with dual
      return t2;                // Return prior
    }
    if( RECURSIVE_MEET > 0 )    // Mid-building recursive types; do not intern
      return this;
    // Not in type table
    _dual = null;                // No dual yet
    INTERN.put(this,this);       // Put in table without dual
    T d = xdual();               // Compute dual without requiring table lookup
    d._hash = d.compute_hash();  // Set dual hash
    _dual = d;
    if( this==d ) return d;      // Self-symmetric?  Dual is self
    if( equals(d) ) { d.free(null); _dual=(T)this; return this; } // If self symmetric then use self
    assert d._dual==null;        // Else dual-dual not computed yet
    assert INTERN.get(d)==null;
    d._dual = (T)this;
    INTERN.put(d,d);
    return this;
  }
  // Remove a forward-ref type from the interning dictionary, prior to
  // interning it again - as a self-recursive type
  @SuppressWarnings("unchecked")
  final T untern( ) {
    Type rez = INTERN.remove(this);
    assert rez != null;
    return (T)this;
  }
  @SuppressWarnings("unchecked")
  final T retern( ) {
    assert _dual._dual == this;
    INTERN.put(this,this);
    assert INTERN.get(this)==this;
    return (T)this;
  }
  boolean interned() { return INTERN.get(this)==this; }
  Type intern_lookup() { return INTERN.get(this); }
  static int intern_size() { return INTERN.size(); }
  static boolean intern_check() {
    for( Type k : INTERN.keySet() )
      if( k.intern_check0() ) return false;
    return true;
  }
  private boolean intern_check0() {
    Type v = INTERN.get(this);
    if( this == v ) return false;
    System.out.println("INTERN_CHECK FAIL: "+_uid+":"+this+" vs "+v._uid+":"+v);
    return true;
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
  static final byte TNUM    = 8; // Number and all derivatives (Complex, Rational, Int, Float, etc)
  static final byte TXNUM   = 9; // Any Numbers; dual of NUM
  static final byte TNNUM   =10; // Numbers-not-nil
  static final byte TXNNUM  =11; // Invert Numbers-not-nil
  static final byte TREAL   =12; // All Real Numbers
  static final byte TXREAL  =13; // Any Real Numbers; dual of REAL
  static final byte TNREAL  =14; // Numbers-not-nil
  static final byte TXNREAL =15; // Invert Numbers-not-nil
  static final byte TNIL    =16; // The Nil-type
  static final byte TSIMPLE =17; // End of the Simple Types
  private static final String[] STRS = new String[]{"all","any","Ctrl","~Ctrl","Scalar","~Scalar","nScalar","~nScalar","Number","~Number","nNumber","~nNumber","Real","~Real","nReal","~nReal","nil"};
  // Complex types - Implemented in subclasses
  static final byte TINT    =18; // All Integers, including signed/unsigned and various sizes; see TypeInt
  static final byte TFLT    =19; // All IEEE754 Float Numbers; 32- & 64-bit, and constants and duals; see TypeFlt
  static final byte TRPC    =20; // Return PCs; Continuations; call-site return points; see TypeRPC
  static final byte TNAME   =21; // Named types; always a subtype of some other type
  static final byte TTUPLE  =22; // Tuples; finite collections of unrelated Types, kept in parallel
  static final byte TOBJ    =23; // Memory objects; arrays and structs and strings
  static final byte TSTRUCT =24; // Memory Structs; tuples with named fields
  static final byte TSTR    =25; // Memory String type; an array of chars
  static final byte TMEM    =26; // Memory type; a map of Alias#s to TOBJs
  static final byte TMEMPTR =27; // Memory pointer type; a collection of Alias#s
  static final byte TFUNPTR =28; // Function pointer, refers to a collection of concrete functions
  static final byte TFUN    =29; // A simple function signature, not a function nor function pointer
  static final byte TLAST   =30; // Type check

  public  static final Type ALL    = make( TALL   ); // Bottom
  public  static final Type ANY    = make( TANY   ); // Top
  public  static final Type CTRL   = make( TCTRL  ); // Ctrl
  public  static final Type XCTRL  = make(TXCTRL  ); // Ctrl
  public  static final Type  SCALAR= make( TSCALAR); // ptrs, ints, flts; things that fit in a machine register
  public  static final Type XSCALAR= make(TXSCALAR); // ptrs, ints, flts; things that fit in a machine register
  public  static final Type  NSCALR= make( TNSCALR); // Scalars-not-nil
          static final Type XNSCALR= make(TXNSCALR); // Scalars-not-nil
  public  static final Type   NIL  = make( TNIL   ); // The Nil.
  private static final Type   NUM  = make( TNUM   );
  private static final Type  XNUM  = make(TXNUM   );
  private static final Type  NNUM  = make( TNNUM  );
  private static final Type XNNUM  = make(TXNNUM  );
  public  static final Type   REAL = make( TREAL  );
  private static final Type  XREAL = make(TXREAL  );
          static final Type  NREAL = make( TNREAL );
  private static final Type XNREAL = make(TXNREAL );

  // Collection of sample types for checking type lattice properties.
  private static final Type[] TYPES = new Type[]{ALL,ANY,CTRL,XCTRL,SCALAR,XSCALAR,NSCALR,XNSCALR,NUM,XNUM,NNUM,XNNUM,REAL,XREAL,NREAL,XNREAL};

  // The complete list of primitive types that are disjoint and also is-a
  // SCALAR; nothing else is a SCALAR except what is on this list (or
  // subtypes).  Useful when type-specializing functions to break SCALAR args
  // into a concrete list of specific types.  Specifically excludes e.g.
  // TypeTuple - these may be passed as a scalar reference type in the future
  // but for now Tuples explicitly refer to multiple values, and a SCALAR is
  // exactly 1 value.
  private static /*final*/ Type[] SCALAR_PRIMS;

  private boolean is_simple() { return _type < TSIMPLE; }
  // Return base type of named types
  public Type base() { Type t = this; while( t._type == TNAME ) t = ((TypeName)t)._t; return t; }
  // Strip off any subclassing just for names
  private byte simple_type() { return base()._type; }
  private boolean is_ptr() { byte t = simple_type();  return t == TFUNPTR || t == TMEMPTR; }
  private boolean is_num() { byte t = simple_type();  return t == TNUM || t == TXNUM || t == TNNUM || t == TXNNUM || t == TREAL || t == TXREAL || t == TNREAL || t == TXNREAL || t == TINT || t == TFLT; }
  // True if 'this' isa SCALAR, without the cost of a full 'meet()'
  private static final byte[] ISA_SCALAR = new byte[]{/*ALL-0*/0,0,0,0,1,1,1,1,1,1,/*TNNUM-10*/1,1,1,1,1,1,1,/*TSIMPLE-17*/0, 1,1,1,1,0,0,0,0,0,1,1,/*TFUN-29*/0}/*TLAST=30*/;
  public final boolean isa_scalar() { assert ISA_SCALAR.length==TLAST; return ISA_SCALAR[_type]!=0; }

  // Return cached dual
  public final T dual() { return _dual; }

  // Compute dual right now.  Overridden in subclasses.
  @SuppressWarnings("unchecked")
  T xdual() {
    assert is_simple();
    if( _type==TNIL ) return (T)this; // NIL is a constant and thus self-dual
    return (T)new Type((byte)(_type^1));
  }
  T rdual() { assert _dual!=null; return _dual; }

  public final Type meet( Type t ) {
    Type mt = xmeet0(t);
    if( _cyclic && t._cyclic && !mt._cyclic ) {
      assert !mt.interned();
      mt._cyclic = true;
    }
    return mt;
  }
  private Type xmeet0( Type t ) {
    // Short cut for the self case
    if( t == this ) return this;
    // Reverse; xmeet 2nd arg is never "is_simple" and never equal to "this"
    return !is_simple() && t.is_simple() ? t.xmeet(this) : xmeet(t);
  }

  // Compute meet right now.  Overridden in subclasses.
  // Handles cases where 'this.is_simple()' and unequal to 't'.
  // Subclassed xmeet calls can assert that '!t.is_simple()'.
  protected Type xmeet(Type t) {
    assert is_simple(); // Should be overridden in subclass
    // ANY meet anything is thing; thing meet ALL is ALL
    if( this==ALL || t==ANY ) return this;
    if( this==ANY || t==ALL ) return    t;

    // Ctrl can only meet Ctrl, XCtrl or Top
    byte type = (byte)(_type|t._type); // the OR is low if both are low
    if(  type <= TXCTRL ) return _type==TXCTRL && t._type==TXCTRL ? XCTRL : CTRL;
    if( _type <= TXCTRL || t._type <= TXCTRL ) return ALL;

    // Meeting scalar and non-scalar falls to ALL.  Includes most Memory shapes.
    if( isa_scalar() ^ t.base().isa_scalar() ) return ALL;

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

    if( _type == TNIL   ) return t.meet_nil();

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
      if( that_num ) {
        // Numeric; same pattern as ANY/ALL, or SCALAR/XSCALAR
        if( _type == TNUM || t._type == TNUM ) return NUM;
        if(   _type == TXNUM ) return t   ;
        if( t._type == TXNUM ) return this;

        // Not-nil variants
        if(   _type == TNNUM ) return t.must_nil() ? NUM : NNUM;
        if( t._type == TNNUM ) return   must_nil() ? NUM : NNUM;
        if(   _type == TXNNUM) return t.not_nil();
        if( t._type == TXNNUM) return   not_nil();

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
    // Named numbers or whatever: let name sort it out
    if( t._type == TNAME  ) return t.xmeet(this);
    throw typerr(t);
  }

  // By design in meet, args are already flipped to order _type, which forces
  // symmetry for things with badly ordered _type fields.  The question is
  // still interesting for other orders.
  private boolean check_commute( Type t, Type mt ) {
    if( t==this ) return true;
    if( is_simple() && !t.is_simple() ) return true; // By design, flipped the only allowed order
    Type mt2 = t.xmeet(this);   // Reverse args and try again
    if( mt==mt2 ) return true;
    System.out.println("Meet not commutative: "+this+".meet("+t+")="+mt+", but "+t+".meet("+this+")="+mt2);
    return false;
  }
  private boolean check_symmetric( Type t, Type mt ) {
    if( t==this ) return true;
    Type ta = mt._dual.xmeet0(t._dual);
    Type tb = mt._dual.xmeet0(  _dual);
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

  // Trim 'this' to being within lower bound 't' and upper bound 't.dual'
  public Type bound( Type t ) {
    if( t.dual().isa(this) && this.isa(t) ) return this;
    return above_center() ? t.dual() : t;
  }

  public static void init0( HashMap<String,Type> types ) {
    types.put("real",REAL);
    types.put("scalar",SCALAR);
    TypeInt.init1(types);
    TypeFlt.init1(types);
    TypeStr.init1(types);
  }

  private static Type[] ALL_TYPES; // Used for tests
  public static Type[] ALL_TYPES() {
    if( ALL_TYPES != null ) return ALL_TYPES;
    Type[] ts =    Type      .TYPES ;
    ts = concat(ts,TypeFlt   .TYPES);
    ts = concat(ts,TypeFunPtr.TYPES);
    ts = concat(ts,TypeInt   .TYPES);
    ts = concat(ts,TypeMem   .TYPES);
    ts = concat(ts,TypeMemPtr.TYPES);
    ts = concat(ts,TypeName  .TYPES);
    ts = concat(ts,TypeObj   .TYPES);
    ts = concat(ts,TypeRPC   .TYPES);
    ts = concat(ts,TypeStr   .TYPES);
    ts = concat(ts,TypeStruct.TYPES);
    ts = concat(ts,TypeTuple .TYPES);
    // Partial order Sort, makes for easier tests later.  Arrays.sort requires
    // a total order (i.e., the obvious Comparator breaks the sort contract),
    // so we hand-roll a simple bubble sort.
    for( int i=0; i<ts.length; i++ )
      for( int j=i+1; j<ts.length; j++ )
        if( ts[j].isa(ts[i]) ) { Type tmp = ts[i]; ts[i] = ts[j]; ts[j] = tmp; }
    return (ALL_TYPES = ts); // Preserve for tests
  }

  static boolean check_startup() {
    Type[] ts = ALL_TYPES();

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


    // Confirm distributivity.  If A isa B, then A.join(C) isa B.join(C)
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
  private static Type[] concat( Type[] ts0, Type[] ts1 ) {
    Type[] ts = Arrays.copyOf(ts0,ts0.length+ts1.length);
    System.arraycopy(ts1,0,ts,ts0.length,ts1.length);
    return ts;
  }

  // True if value is above the centerline (no definite value, ambiguous)
  public boolean above_center() {
    switch( _type ) {
    case TALL:
    case TCTRL:
    case TNUM:    case TNNUM:
    case TREAL:   case TNREAL:
    case TSCALAR: case TNSCALR:
      return false;             // These are all below center, no simple class is on the center
    case TANY:
    case TXCTRL:
    case TXNUM:    case TXNNUM:
    case TXREAL:   case TXNREAL:
    case TXSCALAR: case TXNSCALR:
      return true;              // These are all above center
    default: throw typerr(null);// Overridden in subclass
    }
  }
  // True if value is higher-equal to SOME constant.
  public boolean may_be_con() {
    switch( _type ) {
    case TALL:
    case TSCALAR:  case TNSCALR:
    case TNUM:     case TNNUM:
    case TREAL:    case TNREAL:
    case TCTRL:
      return false;             // These all include not-constant things
    case TANY:
    case TXREAL:   case TXNREAL:
    case TXNUM:    case TXNNUM:
    case TXSCALAR: case TXNSCALR:
    case TXCTRL:
      return true;              // These all include some constants
    default: throw typerr(null);
    }
  }
  // True if exactly a constant (not higher, not lower)
  public boolean is_con() {
    switch( _type ) {
    case TALL:
    case TCTRL:
    case TNNUM:
    case TNUM:
    case TNREAL:
    case TREAL:
    case TNSCALR:
    case TSCALAR:
    case TANY:
    case TXCTRL:
    case TXNNUM:
    case TXNUM:
    case TXNREAL:
    case TXREAL:
    case TXNSCALR:
    case TXSCALAR:
      return false;             // Not exactly a constant
    default: throw typerr(null);// Overridden in subclass
    }
  }
  // Return true if this is a forward-ref function pointer (return type from EpilogNode)
  public boolean is_forward_ref() { return false; }
  // Return the recursive type if this is a forward-ref type def, and null otherwise
  public TypeName merge_recursive_type( Type t ) { return null; }

  // Return a long   from a TypeInt constant; assert otherwise.
  public long   getl() { throw typerr(null); }
  // Return a double from a TypeFlt constant; assert otherwise.
  public double getd() { throw typerr(null); }
  // Return a String from a TypeStr constant; assert otherwise.
  public String getstr() { throw typerr(null); }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  public byte isBitShape(Type t) {
    if( above_center() && isa(t) ) return 0; // Can choose compatible format
    if( _type == t._type ) return 0; // Same type is OK
    if( t._type==TSCALAR ) return 0; // Generic function arg never requires a conversion
    if( _type == TALL || _type == TSCALAR || _type == TNSCALR ) return -1; // Scalar has to resolve
    if( _type == TREAL && t.is_num() ) return -1; // Real->Int/Flt has to resolve

    throw typerr(t);  // Overridden in subtypes
  }
  // "widen" a narrow type for primitive type-specialization.
  // e.g. "3" becomes "int64".
  public Type widen() { return this; } // Overridden in subclasses
  // Operator precedence
  public byte op_prec() { return -1; } // Overridden in subclasses

  // True if type must include a nil (as opposed to may-nil, which means the
  // type can choose something other than nil).
  public boolean must_nil() {
    switch( _type ) {
    case TALL:
    case TNUM:
    case TREAL:
    case TSCALAR:
    case TNIL:
    case TCTRL:  // Nonsense, only for IfNode.value test
    case TXCTRL: // Nonsense, only for IfNode.value test
    case TMEM:   // Nonsense, only for IfNode.value test
      return true;              // These all must include a nil
    case TANY:
    case TXNUM:
    case TXREAL:
    case TXSCALAR:
    case TXNSCALR: case TNSCALR:
    case TXNNUM:   case TNNUM:
    case TXNREAL:  case TNREAL:
      return false;             // These all may be non-nil
    default: throw typerr(null); // Overridden in subclass
    }
  }
  // True if type may include a nil (as opposed to must-nil).
  // True for many above-center or zero values.
  public boolean may_nil() {
    switch(_type) {
    case TALL:
    case TNUM:
    case TREAL:
    case TSCALAR:
    case TXNSCALR: case TNSCALR:
    case TXNNUM:   case TNNUM:
    case TXNREAL:  case TNREAL:
    case TTUPLE:
      return false;
    case TANY:
    case TXNUM:
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
    case TXNUM   :  return XNNUM  ;
    case TXREAL  :  return XNREAL ;
    case TSCALAR:   case TNSCALR:   case TXNSCALR:
    case TNUM:      case TNNUM:     case TXNNUM:
    case TREAL:     case TNREAL:    case TXNREAL:
      return this;
    default: throw typerr(null); // Overridden in subclass
    }
  }
  public Type meet_nil() {
    switch( _type ) {
    case TXNUM:
    case TXREAL:
    case TXSCALAR:  return NIL;
    case TXNNUM:
    case TXNREAL:
    case TXNSCALR:  return TypeInt.BOOL;
    case TNUM:    case TNNUM:     return NUM;
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

  // Mismatched scalar types that can only cross-nils
  Type cross_nil(Type t) { return must_nil() || t.must_nil() ? SCALAR : NSCALR; }

  // Make a (possibly cyclic & infinite) named type.  Prevent the infinite
  // unrolling of names by not allowing a named-type with depth >= D from
  // holding (recursively) the head of a named-type cycle.  We need to cap the
  // unroll, to prevent loops/recursion from infinitely unrolling.
  Type make_recur(TypeName tn, int d, BitSet bs ) { assert is_simple(); return this; }

  // Is t type contained within this?  Short-circuits on a true
  public final boolean contains( Type t ) { return contains(t,null); }
  boolean contains( Type t, BitSet bs ) { return this==t; }
  // Depth of nested types
  public final int depth() { return depth(null); }
  int depth( BitSet bs ) { return 1; }
  // Mark if part of a cycle
  void mark_cycle( Type t, BitSet visit, BitSet cycle ) { }
  // Replace old with nnn in a clone
  Type replace( Type old, Type nnn, HashMap<Type,Type> ignore ) { return this; }

  // Iterate over any nested child types.  Only side-effect results.
  public void iter( Consumer<Type> c ) { /*None in the base class*/ }

  // Apply the test(); if it returns true iterate over all nested child types.
  // If the test returns false, short-circuit the walk.  No attempt to guard
  // against recursive structure walks, so the 'test' must return false when
  // visiting the same Type again.
  void walk( Predicate<Type> p ) { assert is_simple(); p.test(this); }

  TypeStruct repeats_in_cycles(TypeStruct head, BitSet bs) { return null; }

  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.opto() state.
  public Type startype() {
    if( is_con() ) {
      assert dual()==this;
      return dual();
    }
    // Various error codes start high
    return above_center() ? this : dual();
  }

  RuntimeException typerr(Type t) {
    throw new RuntimeException("Should not reach here: internal type system error with "+this+(t==null?"":(" and "+t)));
  }
}
