package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.*;
import java.util.function.*;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

/** A memory-based collection of optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.  Fields
 *  can be indexed by field name or numeric constant (i.e. tuples), but NOT by
 *  a general number - that's an Array.  Fields are matched on name and not
 *  index; field order is irrelevant to named fields.
 *
 *  Structs can be open or closed (and like all Types, high or low).  A struct
 *  acts as-if it has an all possible field names (except those explicitly
 *  mentioned) set to ANY (open) or ALL (closed).  Adding a new field to a
 *  closed struct is a no-op, since such a field already implicitly exists.
 *
 *  The recursive type poses some interesting challenges.  It is represented as
 *  literally a cycle of pointers which must include a TypeStruct (and not a
 *  TypeTuple which only roots Types), a TypeMemPtr (edge) or a TypeFunPtr
 *  (display and return pointers) and a TypeFld.  Type inference involves
 *  finding the Meet of two cyclic structures.  The cycles will not generally
 *  be of the same length.  However, each field Meets independently (and fields
 *  in one structure but not the other use the open/close rules).  This means
 *  we are NOT trying to solve the general problem of graph-equivalence (a
 *  known NP hard problem).  Instead, we can solve each field independently and
 *  also intersect across common fields.
 *
 *  When solving across a single field, we will find some prefix and then
 *  possibly a cycle - conceptually the type unrolls forever.  When doing the
 *  Meet we conceptually unroll both types forever, compute the Meet element by
 *  element... but when both types have looped, we can stop and the discovered
 *  cycle is the Meet's cycle.
 */
public class TypeStruct extends Type<TypeStruct> implements Cyclic, Iterable<TypeFld> {
  static final HashMap<TPair,TypeStruct> MEETS0 = new HashMap<>();

  private boolean _any;         // True=choice/join/high; False=all/meet/low

  // The fields indexed by field name.  Effectively final.
  private Ary<TypeFld> _flds;
  // Type is cyclic.  This is a summary property, not a part of the type, hence
  // is not in the equals nor hash.  Used to optimize non-cyclic access.
  private boolean _cyclic;
  // Max field order number.  This is a summary property not part of the type.
  private short _max_arg;

  TypeStruct init( String name, boolean any ) {
    super.init(name);
    _any = any;
    if( _flds==null ) _flds = new Ary<>(TypeFld.class);
    else _flds.clear();         // No leftover fields from pool
    _cyclic = false;
    _max_arg = DSP_IDX;         // Min of the max
    return this;
  }
  // Shallow clone, not interned.  Fields are referenced, not cloned
  @Override TypeStruct copy() {
    TypeStruct ts = _copy().init(_name,_any);
    for( TypeFld fld : this ) ts.add_fld(fld);
    return ts;
  }

  // --------------------------------------------------------------------------
  // Hash code computation and (cycle) Equals

  // Fairly subtle, because the typical hash code is built up from the hashes of
  // its parts, but the parts are not available during construction of a cyclic type.
  // We can count on the field names and accesses but not field order nor type.
  @Override int static_hash() {
    final int hash0 = (super.static_hash() + 0xcafebabe) ^ (_any?1023:0);
    int hash = hash0;
    for( TypeFld fld : this ) {
      // Can depend on the field name and access, but NOT the type - because recursion.
      // Same hash independent of field visitation order, because the iterator does
      // not make order guarantees.
      hash += (fld._fld.hashCode() + fld._access.hashCode());
      _max_arg = (short)Math.max(_max_arg,fld._order);
    }
    if( hash==0 ) hash = Util.hash_spread(hash0);
    return hash;
  }
  @Override public int compute_hash() { return static_hash(); }

  // Returns 1 for definitely equals, 0 for definitely unequals, and -1 if
  // needing the cyclic test.
  private int cmp( TypeStruct t ) {
    if( !super.equals(t) || len() != t.len() || _any != t._any ) return 0;
    // All fields must be equals
    for( int i=0; i<_flds._len; i++ ) {
      TypeFld fld = _flds._es[i];     // Get in order
      TypeFld fld2 = t.get(fld._fld); // Get by name, not order
      if( fld2==null ) return 0;      // Missing field name
      int cmp = fld.cmp(fld2);
      if( cmp!= 1 ) return cmp; // Fields do not match, or needs a cyclic check
    }
    return 1;                   // Everything is equals, right now
  }

  // Static properties equals, no edges.  Already known to be the same class
  // and not-equals.  May-equal fields are treated as equals
  @Override boolean static_eq( TypeStruct t ) {
    if( !super.equals(t) || len() != t.len() || _any != t._any ) return false;
    for( int i=0; i<_flds._len; i++ ) {
      TypeFld fld1 = _flds._es[i];     // Get in order
      TypeFld fld2 = t.get(fld1._fld); // Get by name, not order
      if( fld2==null || fld1.cmp(fld2)==0 ) return false;
    }
    // If any fields are not interned, assume they might be equal
    return true;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct t) ) return false;
    // While we would like to use the notion of interned Type[] during the
    // normal Type.INTERN check, we also get here during building of cyclic
    // structures for which we'll fall into the cyclic check - as the Type[]s
    // are not interned yet.
    // At least one of these is expected to be interned, and so the cycle bit
    // is correct: it is set if the type is cyclic and cleared otherwise.  This
    // means if 2 cyclic types are being checked, at least one will have the
    // cycle bit set.  Which means that if both bits are cleared, at least one
    // if these types is not cyclic, and a simple recursive-descent test works.
    if( !_cyclic && !t._cyclic ) {
      if( !super.equals(t) || len() != t.len() || _any != t._any ) return false;
      // All fields must be equals
      for( int i=0; i<_flds._len; i++ ) {
        TypeFld fld = _flds._es[i];     // Get in order
        TypeFld fld1 = t.get(fld._fld); // Get by name
        if( fld1==null || fld != fld1 ) return false;
      }
      return true;
    }

    int x = cmp(t);
    if( x != -1 ) return x == 1;
    // Unlike all other non-cyclic structures which are built bottom-up, cyclic
    // types have to be built all-at-once, and thus hash-cons and equality-
    // tested with a cyclic-aware equals check.
    return cycle_equals(t);
  }

  static private final Ary<TypeStruct> CYCLES = new Ary<>(new TypeStruct[0]);
  private TypeStruct find_other() {
    int idx = CYCLES.find(this);
    return idx != -1 ? CYCLES.at(idx^1) : null;
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct t) ) return false;
    int x = cmp(t);             // Check static parts
    if( x != -1 ) return x == 1;// Definitely equals or unequals based on static parts
    TypeStruct t2 = find_other();
    if( t2 !=null ) return t2==t   ; // Already in cycle report equals or not
    TypeStruct t3 = t.find_other();
    if( t3 !=null ) return t3==this; // Already in cycle report equals or not

    int len = CYCLES._len;
    CYCLES.add(this).add(t);
    boolean eq=cycle_equals0(t);
    assert CYCLES._len==len+2;
    CYCLES._len=len;
    return eq;
  }
  private boolean cycle_equals0( TypeStruct t ) {
    // TODO: might get here with more unrelated structs, so need to check eg access, and missing names
    assert len()==t.len();
    for( int i=0; i<_flds._len; i++ ) {
      TypeFld fld = _flds._es[i];     // Get in order
      TypeFld fld1 = t.get(fld._fld); // Get by name
      if( fld1==null ) return false;
      Type t0 = fld._t;
      Type t1 = fld1._t;
      if( t0!=t1 &&                // Normally suffices to test ptr-equals only
          (t0==null || t1==null || // Happens when asserting on partially-built cyclic types
           !t0.cycle_equals(t1)) ) // Must do a full cycle-check
        return false;
    }
    return true;
  }

  // --------------------------------------------------------------------------
  // Factories

  // Unlike other types, TypeStruct might make cyclic types for which a
  // DAG-like bottom-up-remove-dups approach cannot work.
  static { new Pool(TSTRUCT,new TypeStruct()); }
  public static TypeStruct malloc( String name, boolean any ) {
    return POOLS[TSTRUCT].<TypeStruct>malloc().init(name,any);
  }
  public TypeStruct hashcons_free() {
    // All subparts already interned
    if( RECURSIVE_MEET ==0 ) for( TypeFld fld : this ) assert fld.interned();
    return super.hashcons_free();
  }

  // Add a field to an under construction TypeStruct
  public TypeStruct add_fld( TypeFld fld ) {
    assert find(fld._fld)==-1;  // No accidental replacing
    _flds.push(fld);
    return this;
  }

  // Set/replace a field to an under construction TypeStruct
  public TypeStruct set_fld( TypeFld fld ) {
    assert un_interned();       // No mutation if interned
    _flds.set(find(fld._fld),fld);
    return this;
  }

  // Make using the fields, with no struct name, low and closed; typical for a
  // well-known structure.  Might auto-allocate a TypeFld[] - which is a
  // perf-hit in high usage points.  Typically, used this way in tests.
  public static TypeStruct make( TypeFld... flds ) { return make("",false,flds); }
  public static TypeStruct make( String name, boolean any, TypeFld... flds ) {
    TypeStruct ts = malloc(name,any);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts.hashcons_free();
  }
  // Arys are used by the parser
  public static TypeStruct make( String name, boolean any, Ary<TypeFld> flds ) {
    TypeStruct ts = malloc(name,any);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts.hashcons_free();
  }

  // Make a collection of fields, with no display and all with default names and final fields.
  private static TypeStruct _malloc() { return malloc("",false); }
  private TypeStruct add_arg(Type t, int n) { return add_fld(TypeFld.make_arg(t,n)); }
  public static TypeStruct args(Type t1         ) { return _malloc().add_arg(t1,DSP_IDX)                    .hashcons_free(); }
  public static TypeStruct args(Type t1, Type t2) { return _malloc().add_arg(t1,DSP_IDX).add_arg(t2,ARG_IDX).hashcons_free(); }

  // Used to make a few testing constants
  public static TypeStruct make_test( String fld_name, Type t, Access a ) { return make(TypeFld.make(fld_name,t,a,ARG_IDX)); }

  // Add fields from a Type[].  Will auto-allocate the Type[], if not already
  // allocated - which is a perf-hit in high usage points.  Typically, used this
  // way in tests.
  public static TypeStruct make_test( Type... ts ) { return make_test("",ts); }
  public static TypeStruct make_test( String name, Type... ts ) {
    TypeStruct st = malloc(name,false);
    st.add_fld(TypeFld.NO_DISP);
    for( int i=0; i<ts.length; i++ )
      st.add_fld(TypeFld.make_tup(ts[i],ARG_IDX+i));
    return st.hashcons_free();
  }
  // Make 2 fields directly
  public static TypeStruct make_test( String f1, Type t1, String f2, Type t2 ) {
    return TypeStruct.make("",false,TypeFld.make(f1,t1,ARG_IDX),TypeFld.make(f2,t2,ARG_IDX+1));
  }


  // Used to make a few (larger and recursive) testing constants.  Some
  // fields are interned and some are recursive and without a type.
  public static TypeStruct malloc_test( TypeFld... flds ) { return malloc_test("",flds); }
  public static TypeStruct malloc_test( String name, TypeFld... flds ) {
    TypeStruct ts = malloc(name,false);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts.set_hash();
  }

  public int nargs() { return _max_arg+1; }

  // The lattice extreme values.

  // Possibly allocated.  No fields specified.  All fields are possible and
  // might be ALL (error).  The worst possible result.
  public static final TypeStruct ISUSED = make("",false);
  // Unused by anybody, perhaps not even allocated.  No fields specified.
  // All fields are available as ANY.
  public static final TypeStruct UNUSED = ISUSED.dual();

  // A bunch of types for tests
  public  static final TypeStruct POINT = args(TypeFlt.FLT64,TypeFlt.FLT64);
  public  static final TypeStruct NAMEPT= POINT.set_name("Point:");
  public  static final TypeStruct A     = make_test("a",TypeFlt.FLT64,Access.Final);
  private static final TypeStruct C0    = make_test("c",TypeInt.FALSE,Access.Final); // @{c:0}
  private static final TypeStruct D1    = make_test("d",TypeInt.TRUE ,Access.Final); // @{d:1}
  public  static final TypeStruct ARW   = make_test("a",TypeFlt.FLT64,Access.RW   );
  public  static final TypeStruct EMPTY = make();
  public  static final TypeStruct FLT64 = args(TypeFlt.FLT64);     // { flt -> }
  public  static final TypeStruct INT64 = args(TypeInt.INT64);     // { int -> }
  public  static final TypeStruct SCALAR1=args(SCALAR);            // { scalar -> }
  public  static final TypeStruct INT64_INT64= args(TypeInt.INT64,TypeInt.INT64); // { int int -> }
  public  static final TypeStruct INT64_FLT64= args(TypeInt.INT64,TypeFlt.FLT64); // { int flt -> }
  public  static final TypeStruct FLT64_INT64= args(TypeFlt.FLT64,TypeInt.INT64); // { flt int -> }
  public  static final TypeStruct FLT64_FLT64= args(TypeFlt.FLT64,TypeFlt.FLT64); // { flt flt -> }

  // Types for Liveness in slot 0 of TypeMem
  public static final TypeStruct ALIVE = ISUSED, DEAD = UNUSED, LNO_DISP = A;

  // Pile of sample structs for testing
  static final TypeStruct[] TYPES = new TypeStruct[]{ISUSED,POINT,NAMEPT,A,C0,D1,ARW,INT64_INT64,SCALAR1};

  // Dual the flds, dual the tuple.  Return a not-interned thing.
  @Override protected TypeStruct xdual() {
    TypeStruct ts = malloc(_name,!_any);
    for( TypeFld fld : this ) ts.add_fld(fld.dual());
    return ts;
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    assert _hash == compute_hash();
    if( _dual != null ) return _dual;
    assert !interned();
    TypeStruct dual = _dual = malloc(_name,!_any);
    dual._dual = this;          // Stop the recursion
    dual._cyclic = _cyclic;     // Only here for recursive structs
    // Have to add the fields first, then set the hash, then loop over the
    // fields recursing.  xdual'd fields are only shallow.
    for( TypeFld fld : this )
      // Some fields are interned already, some are not.
      dual.add_fld(fld.interned() ? fld._dual : fld.xdual());
    dual._hash = dual.compute_hash();
    // Now set the dual fields properly (using the deep rdual)
    for( int i=0; i<_flds._len; i++ )
      dual._flds.setX(i,_flds.at(i).rdual());
    return dual;
  }

  // Standard Meet.  Types-meet-Types and fld-meet-fld.  Fld strings can be
  // top/bottom for tuples.  Structs with fewer fields are virtually extended
  // with either top or bottom accordingly, to Meet against the other side.
  // Field names only restrict matches and do not affect the algorithm complexity.
  //
  // Types can be in cycles: See Large Comment Above.  We effectively unroll
  // each type infinitely until both sides are cycling and take the GCD of
  // cycles.  Different fields are Meet independently and unroll independently.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TSTRUCT:break;
    case TARY:
    case TFLD:
    case TFLT:
    case TINT:
    case TTUPLE :
    case TFUNPTR:
    case TMEMPTR:
    case TRPC:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeStruct that = (TypeStruct)t;
    // INVARIANT: Both this and that are prior existing & interned.
    assert RECURSIVE_MEET > 0 || (interned() && that.interned());
    // INVARIANT: Both MEETS are empty at the start.  Nothing involved in a
    // potential cycle is interned until the Meet completes.
    assert RECURSIVE_MEET > 0 || (MEETS0.isEmpty());

    // If both are cyclic, we have to do the complicated cyclic-aware meet
    if( _cyclic && that._cyclic )
      return cyclic_meet(that);
    // Recursive but not cyclic; since at least one of these types is
    // non-cyclic.  Normal recursion will bottom-out.

    // Meet the non-recursive parts.
    TypeStruct ts = ymeet(that,false);
    return ts.hashcons_free();
  }

  // Meet all elements that are not-recursive.  Keep fields that exist in both
  // structs; for fields on one side where the other side is high, inject the
  // field directly. The high side is assumed to be infinitely extended with
  // high copies of all fields.  Do not (yet) recursive meet the types.
  // This code is common to both the normal and recursive meet codes.
  private TypeStruct ymeet( TypeStruct that, boolean cyclic ) {
    TypeStruct ts = malloc("",_any&that._any);
    // Fields in both
    for( TypeFld fld : this ) {
      TypeFld tfld = that.get(fld._fld);
      if( tfld != null ) ts.add_fld(cyclic ? TypeFld.cmeet(fld,tfld) : fld.xmeet(tfld));
    }
    // Fields in LHS, and RHS is high (can extend with LHS fields)
    if( that._any )
      for( TypeFld fld : this )
        if( !that.has(fld._fld) )
          ts.add_fld(fld); // Only in LHS and RHS is a high field
    // Fields in RHS, and LHS is high (can extend with RHS fields)
    if( _any )
      for( TypeFld fld : that )
        if( !has(fld._fld) )
          ts.add_fld(fld); // Only in RHS and LHS is a high field
    ts._name = mtname(that,ts); // Set name
    return ts;
  }

  // Recursive meet in progress.
  // Called during class-init.
  private static class TPair {
    TypeStruct _ts0, _ts1;
    private static final TPair KEY = new TPair(null,null);
    static TPair set(TypeStruct ts0, TypeStruct ts1) {KEY._ts0=ts0; KEY._ts1=ts1; return KEY; }
    TPair(TypeStruct ts0, TypeStruct ts1) { _ts0=ts0; _ts1=ts1; }
    @Override public int hashCode() { return (_ts0.hashCode()<<17) | _ts1.hashCode(); }
    @Override public boolean equals(Object o) {
      return _ts0.equals(((TPair)o)._ts0) && _ts1.equals(((TPair)o)._ts1);
    }
  }

  // Both structures are cyclic.  The meet will be "as if" both structures are
  // infinitely unrolled, Meeted, and then re-rolled.  If cycles are of uneven
  // length, the end result will be the cyclic GCD length.
  private TypeStruct cyclic_meet( TypeStruct that ) {
    // Walk 'this' and 'that' and map them both (via MEETS0) to a shared common
    // Meet result.  Only walk the cyclic parts... cyclically.  When visiting a
    // finite-sized part we use the normal recursive Meet.  When doing the
    // cyclic part, we use the normal Meet except we need to use the mapped
    // Meet types.  As part of these Meet operations we can end up Meeting Meet
    // types with each other more than once, or more than once from each side -
    // which means already visited Types might need to Meet again, even as they
    // are embedded in other Types - which leads to the need to use Tarjan U-F
    // to union Types on the fly.

    // See if we have worked on this unique pair before.  If so, the cycle has
    // been closed and just return that prior (unfinished) result.
    TypeStruct mt = MEETS0.get(TPair.set(this,that));
    if( mt != null ) return mt; // Cycle has been closed
    // Do a shallow MEET: meet of field names and _any and all things that can
    // be computed without the cycle.  Some fld._t not filled in yet.
    mt = ymeet(that,true);
    mt._hash = mt.compute_hash(); // Hash is now stable; compute
    MEETS0.put(new TPair(this,that),mt);

    // Since the result is cyclic, we cannot test the cyclic parts for
    // pre-existence until the entire cycle is built.  We can't intern the
    // partially built parts, but we want to use the normal xmeet call - which
    // normally recursively interns.  Turn off interning with the global
    // RECURSIVE_MEET flag.
    RECURSIVE_MEET++;

    // For-all fields do the Meet.  Some are not-recursive and mapped, some
    // are part of the cycle and mapped or not.
    for( TypeFld fld : mt ) {
      TypeFld lff = this.get(fld._fld);
      TypeFld rtf = that.get(fld._fld);
      Type lfi = lff == null ? null : lff._t;
      Type rti = rtf == null ? null : rtf._t;
      Type mti = (lfi==null) ? rti : (rti==null ? lfi : lfi.meet(rti));
      Type mtx = fld._t;        // Prior value, perhaps updated recursively
      Type mts = mtx==null ? mti : mtx.meet(mti); // Meet again
      fld.setX(mts);                      // Finally update
    }
    // Check for repeats right now
    for( TypeStruct ts : MEETS0.values() )
      if( ts!=mt && ts.equals(mt) )
        { mt = ts; break; } // Union together

    // Lower recursive-meet flag.  At this point the Meet 'mt' is still
    // speculative and not interned.
    if( --RECURSIVE_MEET > 0 )
      return mt;                // And, if not yet done, just exit with it
    // Minimize and intern the cyclic result
    return Cyclic.install(mt);
  }

  // Shallow clone, not interned.  Fields are also cloned, but not deeper.
  private TypeStruct _clone() {
    assert interned();
    TypeStruct ts = malloc(_name,_any);
    for( TypeFld fld : this )
      ts.add_fld(fld.malloc_from()); // Shallow field clone
    return ts;
  }

  // Cyclic (complex/slow) interning

  // -------------------------------------------------------------------------
  // Approximate an otherwise endless unrolled sequence of:
  //    ...TMP[alias] -> Struct -> [FunPtr]* -> TMP[alias] -> Struct -> ...
  //
  // We can get endless type growth with recursive types and recursive
  // functions.  Not morally equivalent to HotSpot int-range 'widening', which
  // specifically widens at each Loop Phi (eqv: Lambda.arg_meet), and limits
  // the number of widenings.  Here we get 'widened' at each HM application of
  // class Struct.
  //
  // Approx has 3 main properties, and is heavily asserted for.  I spent
  // several months on various versions of approx which got some, but not all,
  // of these properties right.

  // (1) It monotonically shrinks the Type.  That's the whole point: prevent
  // endless Type growth.  The enforced shrinking generally happens by either
  // chopping off the Type at some depth with a Scalar or by being cyclic.
  // (2) It is self-monotonic: T.isa(T.approx()).
  // (3) It is monotonic: If( A.isa(B) ) Then A.approx.isa(B.approx)
  // (4) The result does not suck.  An easy answer is that approx always
  //     returns Scalar but this gives lousy results.  We'd like endless cyclic
  //     approximations to produce finite cyclic types.

  // CNC 02/18/2022.

  // As of this writing I do not know how to make an approx with all 4
  // properties and I tried really hard.  Here is a test case which is both
  // broken and common: MEETing the 2nd instance of an alias over the first
  // instance (MEET-uphill):
  //
  //   T0:  *[2]@{f0=HI ; f1=*[2]@{f0=LOW; f1=HI}}.  AX0: *[2]@{f0=LOW; f1=AX0$}
  //   T1:  *[2]@{f0=MED; f1=LOW}                    AX1: *[2]@{f0=MED; f1=LOW }
  //
  // We can see that T0 >> T1, and T0 >> AX0 and T1 >> AX1 but AX0 !>>! AX1.
  // In fact the types for f0 only need to be HI >> MED, with LOW being
  // sideways to MED and HI.  Fails property (3).  It is safe to MEET-uphill if
  // the nested f1 field >> T0, and can make a cycle.
  //
  // Another attempt I tried is to MEET-downhill and reach the property that at
  // each instanceof the alias, the preceding type >> the following types.
  // This is relatively easy to do with MEET-downhill, BUT it does not make a
  // finite list: you can have tied repeats indefinitely (fails property (1)).
  // I have simple test cases to demonstrate this in TestApprox.
  //
  // Another attempt is to "chop" off the depth below some distance.  This
  // leads to structures briefly exceeding the length getting chopped and this
  // fails property #4.
  //
  // Most approximations not involving MEET also fail (2) or (3) at some point.
  //
  // Not attempted yet:
  // - HS Widening count: each use of MEET keeps a perfect answer, and a
  //   widening count.  Upon the count being exceeded, the MEET changes flavor,
  //   and all instances of an alias are lumped together.
  // - The HM theory only uses the simple pointers, and all TypeStructs are
  //   MEETd in some kind of TypeMemory.  Without side-effects in the HM theory
  //   this Memory can be trivially global.  With side-effects I'd have to
  //   thread a hidden Memory edge through the HM AST.

  public TypeStruct approx( BitsAlias aliases ) { return approx3(aliases); }
  private static BitsAlias AXALIAS;
  private static final Ary<TypeStruct> AXTS = new Ary<>(TypeStruct.class);

  // -------------------------------------------------------------------------
  // Extend-and-approx.  Assert that there is some prefix (the extend) ahead
  // of instances of 'aliases', and that alias instances have the right
  // property: there are 0 or 1 structs targeted by alias.
  public TypeStruct approx3( BitsAlias aliases ) {
    AXALIAS=aliases;

    // Hunt instances of aliases reachable from this struct.
    TypeStruct ts = this;
    while( true ) {
      AXVISIT3.clear();  AXTS.clear();
      ts._apx3a(ts,0);
      // Meet all the deep instances with this shallow instance.
      TypeStruct apx = ts;
      while( AXTS._len>0 ) {
        TypeStruct axts = AXTS.pop();
        TypeMemPtr fail=axts.ax_chk3(axts);
        if( fail!=null )
          return null;            // Lacks the crucial invariant already
        apx = (TypeStruct)apx.meet(axts);
      }

      // Assert all the right properties hold.
      if( ts==apx ) break;
      ts=apx;
      TypeMemPtr fail = ts.ax_chk3(ts);
      if( fail==null ) {
        assert this.isa(apx);   // Self monotonic
        return ts;
      }
    }

    assert RECURSIVE_MEET==0 && MEETS0.isEmpty() && AXOLD2NEW.isEmpty() && AXTS.isEmpty();
    TypeStruct apx = (TypeStruct)ts._apx3b(ts,0);
    MEETS0.clear();  AXOLD2NEW.clear(true);
    apx = Cyclic.install(apx);

    assert this.isa(apx);   // Self monotonic
    return apx;
  }

  private Type _apx3a( Type t, int depth ) {
    assert depth<100;       // Stop stack overflow early, much easier debugging
    if( !(t instanceof Cyclic cyc) ) return null;
    if( AXVISIT3.tset(t._uid) ) return null;
    if( t instanceof TypeMemPtr tmp && tmp._aliases.overlaps(AXALIAS) && tmp._obj!=this )
      AXTS.push(tmp._obj);      // Record other guy for later meet
    return cyc.walk1((fld,ignore) -> _apx3a(fld,depth+1), (x,y)-> null);
  }

  private Type _apx3b( Type old, int depth ) {
    assert depth<100;  // Stop stack overflow early, much easier debugging
    if( !(old instanceof Cyclic) ) return old;
    if( old instanceof TypeMemPtr tmp ) {
      Type dup = AXOLD2NEW.get(old._uid);
      if( dup!=null ) return dup; // Dup check: been here, done that.

      if( AXALIAS.overlaps(tmp._aliases) ) {
        TypeMemPtr nnn = tmp.copy();
        AXOLD2NEW.put(old._uid, nnn);  // Make a copy; copy is NOT interned and IS in the dup check.
        nnn._obj = (TypeStruct)AXOLD2NEW.get(_uid);// Make a self-cycle
        return nnn;
      }
    }
    Type nnn = old.copy();
    AXOLD2NEW.put(old._uid, nnn);  // Make a copy; copy is NOT interned and IS in the dup check.

    // Recurse
    ((Cyclic)nnn).walk_update(fld -> _apx3b(fld,depth+1));
    return nnn;
  }


  // Check for invariant: there are no ptrs-of-alias except to *this*
  private static final VBitSet AXVISIT3 = new VBitSet();
  private TypeMemPtr ax_chk3(Type t) {  AXVISIT3.clear();  return _ax_chk3(t); }
  private TypeMemPtr _ax_chk3(Type t) {
    if( !(t instanceof Cyclic cyc) ) return null;
    if( AXVISIT3.tset(t._uid) ) return null;
    if( t instanceof TypeMemPtr tmp && tmp._aliases.overlaps(AXALIAS) && tmp._obj!=this )   return tmp;
    return cyc.walk1((fld,ignore) -> _ax_chk3(fld), (x,y)-> x==null ? y : x);
  }


  // -------------------------------------------------------------------------
  // Has properties 2,3,4 but not #1: does not limit depth to some finite amount.
  private TypeStruct approx2( BitsAlias aliases ) {
    //// Fast-path cutout for boring structs
    //boolean shallow=true;
    //for( int i=0; i<_flds._len; i++ ) {
    //  TypeFld fld = _flds._es[i];
    //  if( fld._t instanceof TypeMemPtr ||
    //      (fld._t instanceof TypeFunPtr tfp && !tfp._ret.is_simple()) )
    //    { shallow=false; break; }
    //}
    //if( shallow ) return this; // Fast cutout for boring structs

    // Repeat until every instance of alias ISA the next instance of alias.
    TypeStruct ts=this;
    AXALIAS = aliases;
    while(true) {
      assert RECURSIVE_MEET==0 && MEETS0.isEmpty() && AXOLD2NEW.isEmpty();
      TypeMemPtr ptmp = TypeMemPtr.make(aliases,ts);
      TypeStruct apx = ((TypeMemPtr)_apx2(ptmp,null,null,0))._obj;
      MEETS0.clear();  AXOLD2NEW.clear(true);
      apx = Cyclic.install(apx);
      assert ts.isa(apx);       // Self monotonic
      ts = apx;
      TypeMemPtr ctmp = TypeMemPtr.make(aliases,apx);
      Type ax_chk=_ax_chk(new VBitSet(),ctmp,null,aliases);
      if( ax_chk==null ) break; // Repeat until invariant holds
    }

    // This version fails to limit the depth.  I.e., it fails to approximate.

    return ts;
  }

  // Algo theory:
  // - Track prior TMP with alias, called PAX, and perhaps a new TMP with alias called NAX.
  // - Walk the type, constructing (recursively) a new type in parallel with the old.
  // - If no TMP with alias, just recursively 'make'; Else
  // - If PAX isa TMP, then invariant already holds, just recursively 'make'; Else
  // - If TMP isa PAX, then use NAX instead of TMP and immediately return making a cycle; Else
  // - Meet PAX with TMP (all interned), and begin walking this as the new OLD side.

  // At the end of apx2, one-nested-depth of instances of alias have the isa
  // property, but perhaps not deeper instances if the original type had
  // several out-of-order.

  private static final NonBlockingHashMapLong<Type> AXOLD2NEW = new NonBlockingHashMapLong<>();
  private static Type _apx2( Type old, TypeMemPtr pax, TypeMemPtr nax, int depth ) {
    assert depth<100;  // Stop stack overflow early, much easier debugging

    if( !(old instanceof Cyclic) ) return old;

    TypeMemPtr tmp = old instanceof TypeMemPtr tmp2 && AXALIAS.overlaps(tmp2._aliases) ? tmp2 : null;
    if( pax!=null && tmp!=null ) {
      Type mt = tmp.meet(pax);
      if( mt==pax/*tmp.isa.pax*/ ) return nax; // Push new version of pax, no need to meet-over since ISA means no progress
      if( mt!=tmp/*pax.isa.tmp*/ ) // Missing invariant
        old = tmp = (TypeMemPtr)mt; // Force invariant in old-side before walking
    }
    if( old instanceof TypeMemPtr ) {
      Type nnn = AXOLD2NEW.get(old._uid);
      if( nnn!=null ) return nnn; // Dup check: been here, done that.
    }
    // Clone
    Type fnnn = old.copy();
    if( old instanceof TypeMemPtr )
      AXOLD2NEW.put(old._uid, fnnn );  // Make a copy; copy is NOT interned and IS in the dup check.

    // Recurse; If new overlap point swap pax/nax
    final TypeMemPtr ftmp = tmp;
    ((Cyclic)fnnn).walk_update(fld -> _apx2(fld,
                                            ftmp==null ? pax : ftmp,
                                            ftmp==null ? nax : (TypeMemPtr)fnnn,depth+1));
    return fnnn;
  }

  // Check that the invariant holds: if T is a TMP_aliases.overlaps(aliases),
  // (and prior is also), then prior.isa(T).
  private static TypeMemPtr _ax_chk(VBitSet visit, Type t, TypeMemPtr prior, BitsAlias aliases) {
    if( !(t instanceof Cyclic cyc) ) return null; // No fail
    final TypeMemPtr fprior;
    if( t instanceof TypeMemPtr tmp && tmp._aliases.overlaps(aliases) ) {
      if( prior!=null && !prior.isa(tmp) )
        return tmp; // Fail
      else fprior = tmp;
    } else fprior = prior;
    if( t instanceof TypeStruct && visit.tset(t._uid) ) return null; // Cycled; no fail
    return cyc.walk1((fld,ignore) -> _ax_chk(visit,fld,fprior,aliases), (x,y)-> x==null ? y : x);
  }


  @Override public TypeStruct simple_ptr() {
    TypeStruct ts = malloc(_name,_any);
    for( TypeFld fld : this ) {
      Type t = fld._t.simple_ptr();
      ts.add_fld(t==fld._t ? fld : fld.make_from(t));
    }
    return ts.hashcons_free();
  }

  // ------ Utilities -------
  // All fields for iterating.
  public int len() { return _flds._len; } // Count of fields
  // Find index by name
  public int find( String name ) {
    for( int i=0; i<_flds._len; i++ )
      if( Util.eq(name,_flds._es[i]._fld) )
        return i;
    return -1;
  }
  // Field by name.
  public boolean has( String name ) { return find(name)!=-1; }
  public TypeFld get( String name ) {
    int idx = find(name);
    return idx==-1 ? null : _flds._es[idx];
  }
  public TypeFld put( TypeFld fld ) {
    int idx = find(fld._fld);
    if( idx==-1 ) { _flds.push(fld); return null; }
    return _flds.set(idx,fld);  // Return old value
  }
  // Field type.  NPE if field-not-found
  public Type at( String name ) { return get(name)._t; }

  public TypeFld fld_idx( int idx, int aidx ) {
    TypeFld fld = _flds.atX(idx);
    if( fld==null ) return null;
    assert fld._order==aidx;
    return fld;
  }
  // debug interface
  public TypeFld _fld_idx( int idx ) { return _flds.at(idx); }

  // Non-allocating iterator; pulls iterators from a pool.  The hard part is
  // telling when an iterator ends early, to avoid leaking.  This is not
  // exactly asserted for, so some leaks may happen.
  @Override public Iter iterator() { return Iter.get(this); }
  private static class Iter implements Iterator<TypeFld> {
    private static final Ary<Iter> POOL = new Ary<>(Iter.class);
    private static int CNT=0; // Number of Iters made, helps to track leaks
    Ary<TypeFld> _flds;
    boolean _has_hash;
    int _i;
    static Iter get(TypeStruct ts) {
      if( POOL.isEmpty() ) { assert CNT<100; CNT++; new Iter().end(); }
      return POOL.pop().init(ts);
    }
    boolean end() { _i=-99; _flds=null; POOL.push(this); return false; }
    private Iter init(TypeStruct ts) { assert _i==-99; _i=0; _flds=ts._flds; _has_hash = ts._hash!=0; return this; }
    @Override public boolean hasNext() {  assert _i>=0; return _i < _flds._len || end(); }
    @Override public TypeFld next() { return _flds._es[_i++]; }
    @Override public void remove() {
      // i was pre-advanced, so remove field i-1
      assert !_has_hash;          // Changing, so underlying struct is mid-construction
      _flds.remove(--_i);
    }
  }

  @Override public <T> T walk1( BiFunction<Type,String,T> map, BinaryOperator<T> reduce ) {
    T rez=null;
    for( TypeFld fld : this ) {
      T rez2 = map.apply(fld,fld._fld);
      rez = rez==null ? rez2 : reduce.apply(rez,rez2);
    }
    return rez;
  }
  @Override public void walk_update(    UnaryOperator<Type> map ) { for( int i=0; i<_flds._len; i++ ) _flds._es[i] = (TypeFld)map.apply(_flds._es[i]); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    TypeStruct ts = (TypeStruct)t;
    Cyclic.Link lk = null;
    for( TypeFld fld0 : this ) {
      TypeFld fld1 = ts.get(fld0._fld);
      if( fld1==null ) throw unimpl(); // different here
      Cyclic.Link dlk = Cyclic._path_diff(fld0,fld1,links);
      if( dlk==null || dlk._t0==null ) continue; // No difference
      lk = Cyclic.Link.min(lk,dlk); // Min depth
    }
    return lk;
  }

  static boolean isDigit(char c) { return '0' <= c && c <= '9'; }
  public boolean is_tup() {
    if( len()==0 || (len()==1 && get("^")!=null) ) return true;
    return get("0")!=null;
  }

  @Override void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"S"+(char)('A'+ucnt._ts++));
      return;
    }
    for( TypeFld fld : this )
      if( fld!=null )
        fld._str_dups(visit,dups,ucnt);
  }

  @SuppressWarnings("unchecked")
  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    // Special shortcut for the all-prims display type
    if( get("pi") != null ) {
      sb.p("MATH");
    } else {
      // Set the indent flag once for the entire struct.  Indent if any field is complex.
      boolean ind = false;
      for( TypeFld fld : this )
        if( (debug || !Util.eq(fld._fld,"^")) && (fld._t!=null && fld._t._str_complex(visit,dups)) )
          ind=indent;           // Field is complex, indent if asked to do so
      if( ind ) sb.ii(1);
      boolean field_sep=false;
      for( TypeFld fld : indent ? _flds : asorted_flds() ) {
        if( !debug && Util.eq(fld._fld,"^") ) continue; // Do not print the ever-present display
        if( ind ) sb.nl().i();
        fld._str(visit,dups, sb, debug, indent ); // Field name, access mod, type
        sb.p(is_tup ? ", " : "; "); // Between fields
        field_sep=true;
      }
      if( field_sep ) sb.unchar().unchar();
      if( ind ) sb.nl().di(1).i();
    }
    sb.p(!is_tup ? "}" : ")");
    return sb;
  }

  @Override boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) { return true; }

  // e.g. (), (^=any), (^=any,"abc"), (3.14), (3.14,"abc"), (,,)
  static TypeStruct valueOf(Parse P, String cid, boolean is_tup, boolean any ) {
    if( is_tup ) P.require('(');
    else { P.require('@');  P.require('{'); }
    TypeStruct ts = malloc("",any);
    if( cid!=null ) P._dups.put(cid,ts);
    if( P.peek(!is_tup ? '}' : ')') ) return ts;

    int aidx=DSP_IDX;
    do {
      TypeFld fld=null;
      int oldx = P._x;
      String fid = P.id();
      Type dup = P._dups.get(fid);
      if( dup==null ) {
        // Check for a leading repeat name, even on a tuple: "FA:^=any"
        if( fid.length()!=0 && P.peek(':') && (!is_tup || aidx==DSP_IDX) )
          RECURSIVE_MEET++;     // Start a cyclic field type
        else { P._x = oldx; fid=null; }
        // Check for "^=any" on *tuples* which do not normally print field names
        if( aidx==DSP_IDX ) {
          fld = TypeFld.valueOfArg(P, aidx, fid);
          if( fld==null ) aidx++; // Parse "(int64)" correct; tuple with leading id not field name
        }
        if( fld==null )         // Parse a field
          fld = is_tup ? TypeFld.valueOfTup(P,aidx,fid) : TypeFld.valueOfArg(P,aidx,fid);

        if( fid!=null ) --RECURSIVE_MEET; // End cyclic field type
        fld = P.cyc(fld);                 // Install as needed
      } else {                  // Hit a duplicate
        // Ambiguous with un-named tuple fields
        fld = dup instanceof TypeFld dup2 ? dup2
          : TypeFld.malloc(TypeFld.TUPS[aidx==DSP_IDX ? ARG_IDX : aidx],dup,Access.Final,aidx==DSP_IDX ? ARG_IDX : aidx);
      }

      aidx++;
      ts.add_fld(fld);

    } while( P.peek(is_tup ? ',' : ';') );
    P.require(is_tup ? ')' : '}');
    return ts;
  }

  // Alpha sorted
  public Collection<TypeFld> asorted_flds() {
    TreeMap<String, TypeFld> sorted = new TreeMap<>();
    for( TypeFld fld : this ) sorted.put(fld._fld,fld);
    return sorted.values();
  }
  // Field order sorted
  public Collection<TypeFld> osorted_flds() {
    TreeMap<String, TypeFld> sorted = new TreeMap<>(Comparator.comparingInt(f0 -> get(f0)._order));
    for( TypeFld fld : this ) sorted.put(fld._fld,fld);
    return sorted.values();
  }

  @Override public boolean cyclic() { return _cyclic; }
  @Override public void set_cyclic() { _cyclic = true; }
  @Override public void clr_cyclic() { _cyclic = false; }

  // Extend the current struct with a new named field, making a new struct
  public TypeStruct add_fldx( TypeFld fld ) { return copy().add_fld(fld).hashcons_free(); }
  // Replace an existing field in the current struct.
  public TypeStruct replace_fld( TypeFld fld ) {
    if( get(fld._fld)==fld ) return this;
    return copy().set_fld(fld).hashcons_free();
  }
  public TypeStruct pop_fld(int idx) {
    TypeStruct ts = copy();
    TypeFld fld = ts._flds.pop();
    assert fld._order==idx;
    return ts.hashcons_free();
  }

  // Update (approximately) the current TypeObj.  Updates the named field.
  public TypeStruct update(Access fin, String fld, Type val) { return update(fin,fld,val,false); }

  TypeStruct update(Access fin, String name, Type val, boolean precise) {
    TypeFld fld = get(name);
    if( fld == null ) return this; // Unknown field, assume changes no fields
    // Double-final-stores, result is an error
    if( fld._access==Access.Final || fld._access==Access.ReadOnly )
      val = Type.ALL;
    // Pointers & Memory to a Store can fall during GCP, and go from r/w to r/o
    // and the StoreNode output must remain monotonic.  This means store
    // updates are allowed to proceed even if in-error.
    //if( fin==Access.Final || fin==Access.ReadOnly ) precise=false;
    Type   pval = precise ? val : fld._t.meet(val);
    Access pfin = precise ? fin : fld._access.meet(fin);
    return replace_fld(fld.make_from(pval,pfin));
  }

  public TypeStruct flatten_fields() {
    TypeStruct ts = malloc(_name,_any);
    for( TypeFld fld : this )
      ts.add_fld(fld.make_from(fld._t==Type.XSCALAR||fld._t==Type.ANY ? Type.XSCALAR : Type.SCALAR,Access.bot()));
    return ts.hashcons_free();
  }

  // Used during liveness propagation from Loads.
  // Fields not-loaded are not-live.
  TypeStruct remove_other_flds(String name, Type live) {
    TypeFld nfld = get(name);
    if( nfld == null ) return UNUSED; // No such field, so all fields will be XSCALAR so UNUSED instead
    TypeStruct ts = _clone();
    for( TypeFld fld : ts )
      ts.put(fld.setX( Util.eq(fld._fld,name) ? live : XSCALAR, Access.bot()).hashcons_free());
    return ts.hashcons_free();
  }

  // Widen (lose info), to make it suitable as the default function memory.
  // All fields are widened to ALL (assuming a future error Store); field flags
  // set to bottom; only the field names are kept.
  public TypeStruct crush() {
    if( _any ) return this;     // No crush on high structs
    TypeStruct st = malloc(_name,false);
    // Widen all fields, as-if crushed by errors, even finals.
    for( TypeFld fld : this )
      // Keep only the display pointer, as it cannot be stomped even with error code
      st.add_fld( Util.eq("^",fld._fld) ? fld : fld.make_from(Type.ALL,Access.bot()));
    return st.hashcons_free();
  }

  // Keep field names and orders.  Widen all field contents, including finals.
  // Handles cycles
  @Override TypeStruct _widen() {
    TypeStruct ts = WIDEN_HASH.get(_uid);
    if( ts!=null ) { ts._cyclic=true; return ts; }
    RECURSIVE_MEET++;
    ts = malloc(_name,_any);
    WIDEN_HASH.put(_uid,ts);
    for( TypeFld fld : this ) ts.add_fld(fld.malloc_from());
    ts.set_hash();
    for( TypeFld fld : ts ) fld.setX(fld._t._widen());
    if( --RECURSIVE_MEET == 0 )
      ts = Cyclic.install(ts);
    return ts;
  }

  @Override public boolean above_center() { return _any; }

  @Override public Type meet_nil(Type nil) { return this; }

  @Override boolean contains( Type t, VBitSet bs ) {
    if( bs==null ) bs=new VBitSet();
    if( bs.tset(_uid) ) return false;
    for( TypeFld fld : this ) if( fld._t==t || fld._t.contains(t,bs) ) return true;
    return false;
  }

  @Override public void walk( Predicate<Type> p ) {
    if( p.test(this) )
      for( TypeFld fld : this ) fld.walk(p);
  }

  // Make a Type, replacing all dull pointers from the matching types in mem.
  @Override public TypeStruct make_from(Type head, TypeMem mem, VBitSet visit) {
    if( visit.tset(_uid) ) return null;
    TypeStruct ts = malloc(_name,_any);
    for( TypeFld fld : this )
      ts.add_fld(fld.make_from(head,mem,visit));
    return ts.hashcons_free();
  }

  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    BitsFun fidxs = BitsFun.EMPTY;
    for( TypeFld fld : this )
      fidxs = fidxs.meet(fld._t._all_reaching_fidxs(tmem));
    return fidxs;
  }

  // Used for assertions
  @Override boolean intern_check1() {
    for( TypeFld fld : this )
      if( fld.intern_get()==null )
        return false;
    return true;
  }
}
