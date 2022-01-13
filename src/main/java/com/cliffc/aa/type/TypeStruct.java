package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;

import org.jetbrains.annotations.NotNull;

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
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
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

  private static final Ary<TypeStruct> CYCLES = new Ary<>(new TypeStruct[0]);
  private TypeStruct find_other() {
    int idx = CYCLES.find(this);
    return idx != -1 ? CYCLES.at(idx^1) : null;
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    int x = cmp(t);
    if( x != -1 ) return x == 1;
    TypeStruct t2 = find_other();
    if( t2 !=null ) return t2==t   ; // Already in cycle report equals or not
    TypeStruct t3 = t.find_other();
    if( t3 !=null ) return t3==this;// Already in cycle report equals or not

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
  // perf-hit in high usage points.  Typically used this way in tests.
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
  //// Used by tests only, so ... is ok.
  //public static TypeStruct tups(Type... ts ) {
  //  TypeStruct st = make0();
  //  for( int i=0; i<ts.length; i++ )
  //    st.add_fld(TypeFld.make_tup(ts[i],ARG_IDX+i));
  //  return st.hashcons_free();
  //}

  // Used to make a few testing constants
  public static TypeStruct make_test( String fld_name, Type t, Access a ) { return make(TypeFld.make(fld_name,t,a,ARG_IDX)); }

  // Add fields from a Type[].  Will auto-allocate the Type[], if not already
  // allocated - which is a perf-hit in high usage points.  Typically used this
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


  // Used to make a few (larger and recursive) testing constants.  Some of the
  // fields are interned and some are recursive and without a type.
  public static TypeStruct malloc_test( TypeFld... flds ) { return malloc_test("",flds); }
  public static TypeStruct malloc_test( String name, TypeFld... flds ) {
    TypeStruct ts = malloc(name,false);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts.set_hash();
  }

  // Used by NewNode
  public TypeStruct make_from( IntFunction<Type> gen ) {
    TypeStruct ts = malloc(_name,_any);
    for( TypeFld fld : _flds ) ts._flds.push(fld.make_from(gen.apply(fld._order)));
    return ts.hashcons_free();
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
    // Have to add the fields first, then set the hash, then loop over the fields recursing.
    for( TypeFld fld : this )
      // Some fields are interned already, the cyclic ones are not.
      dual.add_fld(fld.interned() ? fld._dual : fld.xdual());
    dual._hash = dual.compute_hash();
    for( TypeFld fld : this )
      // Some fields are interned already, the cyclic ones are not.
      if( !fld.interned() )
        dual.set_fld(fld.rdual());
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
    // non-cyclic normal recursion will bottom-out.

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
  private static final HashMap<TPair,TypeStruct> MEETS0 = new HashMap<>();

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
    MEETS0.clear();
    // Minimize and intern the cyclic result
    return mt.install();
  }

  // Shallow clone, not interned.  Fields are also cloned, but not deeper.
  private TypeStruct _clone() {
    assert interned();
    TypeStruct ts = malloc(_name,_any);
    for( TypeFld fld : this )
      ts.add_fld(fld.malloc_from()); // Shallow field clone
    return ts;
  }

  // -------------------------------------------------------------------------
  // Approximate an otherwise endless unrolled sequence of:
  //    ...TMP[alias] -> Struct -> [FunPtr]* -> TMP[alias] -> Struct -> ...
  public TypeStruct approx( int cutoff, BitsAlias aliases ) { return approx2(cutoff,aliases); }

  // By chopping off the endless tail, pulling it back one recursion layer and
  // meeting.  This forces unrolled part to look like the cyclic part (at least
  // past the cutoff), which then re-rolls.  Used to prevent endless growth of
  // otherwise cyclic types.

  /**
   This version is NOT associative with meet: A.apx.B != A.B.apx

  "Wrap-and-Approx" is not monotonic!  Can only happen if we have a nested
  instance of alias#12.  This can happen from an ordinary MEET.

  [12]@{                               [12]@{
    pred=~scalar                         pred=~scalar
    succ= *[12]@{     >>> FALLS >>>      succ= scalar // Succ field falls
      pred=*[12]@{ something }         }
    }
  }

  ----- Approx on [12] for both types: -----
  [12]@{                               [12]@{
    pred= $recursive$  <<< LIFTS <<<     pred=~scalar
    succ= $recursive$                    succ= scalar
  }                                    }

  */

  private static final IHashMap OLD2APX = new IHashMap();
  private static final Ary<TypeMemPtr> CUTOFFS = new Ary<>(TypeMemPtr.class);
  public TypeStruct approx1( int cutoff, BitsAlias aliases ) {
    // Fast-path cutout for boring structs
    boolean shallow=true;
    for( TypeFld fld : this )
      if( fld._t instanceof TypeMemPtr ||
          (fld._t instanceof TypeFunPtr && !((TypeFunPtr)fld._t)._ret.is_simple()) )
        { shallow=false; break; }
    if( shallow ) return this;  // Fast cutout for boring structs
    TypeMemPtr ptr = TypeMemPtr.make(aliases,this);

    while( true ) {
      int max = ptr.max(ptr.depth());
      if( max < cutoff )
        return ptr._obj;
      // Scan the old copy for elements that are too deep.
      // 'Meet' those into the clone at one layer up.
      RECURSIVE_MEET++;
      assert OLD2APX.isEmpty() && MEETS0.isEmpty() && CUTOFFS.isEmpty();
      TypeMemPtr apxptr = ax_impl_ptr( aliases, cutoff, 0, ptr, ptr );
      assert CUTOFFS.isEmpty();
      OLD2APX.clear();  MEETS0.clear();
      RECURSIVE_MEET--;
      // apxptr may die/recycle at install, and may include e.g. nil where the
      // original aliases do not
      BitsAlias aliases2 = apxptr._aliases;
      // Remove any leftover internal duplication.
      TypeStruct rez = apxptr._obj.install();
      assert this.isa(rez);
      ptr = TypeMemPtr.make(aliases2,rez);
    }
  }

  // Make a new TypeStruct which is the merge of the original TypeStruct with
  // the too-deep parts merged into shallower parts.
  private static TypeStruct ax_impl_struct( BitsAlias aliases, int cutoff, int d, TypeMemPtr dold, TypeStruct old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeStruct nt = OLD2APX.get(old);
    if( nt != null ) return nt;

    // Clone the old, to make the approximation into
    TypeStruct nts = old._clone();
    OLD2APX.put(old,nts);
    for( TypeFld fld : old ) {
      Type t = fld._t;
      if( t instanceof TypeMemPtr )
        nts.get(fld._fld).setX(ax_impl_ptr (aliases,cutoff,d,dold,(TypeMemPtr)t));
      else if( t instanceof TypeFunPtr )
        nts.get(fld._fld).setX(ax_impl_fptr(aliases,cutoff,d,dold,(TypeFunPtr)t));
    }
    OLD2APX.remove(old); // Do not keep sharing the "tails"
    return nts;
  }

  private static TypeMemPtr ax_impl_ptr( BitsAlias aliases, int cutoff, int d, TypeMemPtr dold, TypeMemPtr old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeMemPtr nt = OLD2APX.get(old);
    if( nt != null ) return nt;

    boolean news = old._aliases.overlaps(aliases);
    if( news ) {              // Depth-increasing pointer?
      if( d==cutoff ) {       // Cannot increase depth any more
        CUTOFFS.push(old);    // Save cutoff point for later MEET
        return OLD2APX.get(dold); // Return last valid depth - forces cycle
      } else {
        assert CUTOFFS.isEmpty();
      }
      d++;              // Increase depth
      dold = old;       // And this is the last TypeMemPtr seen at this depth
    }

    // Walk internal structure, meeting into the approximation
    TypeMemPtr nmp = old.copy();
    OLD2APX.put(old,nmp);
    nmp._obj = ax_impl_struct(aliases, cutoff,d,dold,old._obj);
    if( news && d==cutoff ) {
      while( !CUTOFFS.isEmpty() ) { // At depth limit, meet with cutoff to make the approximation
        Type mt = ax_meet(new BitSetSparse(), nmp, CUTOFFS.pop());
        assert mt==nmp;
      }
    }
    OLD2APX.remove(old);      // Do not keep sharing the "tails"
    return nmp;
  }
  private static Type ax_impl_fptr( BitsAlias aliases, int cutoff, int d, TypeMemPtr dold, TypeFunPtr old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeFunPtr nt = OLD2APX.get(old);
    if( nt != null ) return nt;
    if( old.dsp()!=Type.ANY && old.dsp()!=ALL ) {
      // Walk internal structure, meeting into the approximation
      nt = old.copy();
      OLD2APX.put(old,nt);
      nt.set_dsp(ax_impl_ptr(aliases,cutoff,d,dold,(TypeMemPtr)old.dsp()));
      OLD2APX.put(old,null);      // Do not keep sharing the "tails"
    }
    if( old._ret instanceof TypeMemPtr || old._ret instanceof TypeFunPtr ) {
      // Walk internal structure, meeting into the approximation
      if( nt==null ) nt = old.copy();
      OLD2APX.put(old,nt);
      if( old._ret instanceof TypeMemPtr )
        nt._ret = ax_impl_ptr (aliases,cutoff,d,dold,(TypeMemPtr)old._ret);
      else
        nt._ret = ax_impl_fptr(aliases,cutoff,d,dold,(TypeFunPtr)old._ret);
      OLD2APX.remove(old);      // Do not keep sharing the "tails"
    }
    return nt==null ? old : nt;
  }

  // Update-in-place 'meet' of pre-allocated new types.  Walk all the old type
  // and meet into the corresponding new type.  Changes the internal edges of
  // the new types, so their hash remains undefined.
  private static Type ax_meet( BitSetSparse bs, Type nt, Type old ) {
    assert old.interned();
    if( nt.interned() ) {
      Type xt = nt.meet(old);
      // A complete (non-cyclic) type might attempt interning and get a hash.
      // Remove it and preserve the no-hash-if-not-interned invariant.
      if( !xt.interned() ) xt._hash=0;
      return xt;
    }
    assert nt._hash==0;         // Not definable yet, as nt may yet pick up fields
    if( nt == old ) return old;
    if( old instanceof Cyclic && ((Cyclic)old).cyclic() && bs.tset(nt._uid,old._uid) )
      return nt; // Been there, done that

    // TODO: Make a non-recursive "meet into".
    // Meet old into nt
    switch( nt._type ) {
    case TSCALAR: break; // Nothing to meet
    case TFUNPTR: {
      TypeFunPtr nptr = (TypeFunPtr)nt;
      if( old == Type.NIL || old == Type.XNIL ) return nptr.ax_meet_nil(old);
      if( old == Type.SCALAR ) return old;
      if( old == Type.XSCALAR || old == Type.XNSCALR ) break; // Result is the nt unchanged
      if( !(old instanceof TypeFunPtr) ) throw AA.unimpl(); // Not a xscalar, not a funptr, probably falls to scalar
      TypeFunPtr optr = (TypeFunPtr)old;
      nptr._fidxs = nptr._fidxs.meet(optr._fidxs);
      // While structs normally meet, function args *join*, although the return still meets.
      nptr.set_dsp(ax_meet(bs,nptr.dsp(),optr.dsp()));
      nptr._ret  = ax_meet(bs,nptr._ret ,optr._ret ) ;
      break;
    }
    case TMEMPTR: {
      TypeMemPtr nptr = (TypeMemPtr)nt;
      if( old == Type.NIL || old == Type.XNIL ) return nptr.ax_meet_nil(old);
      if( old == Type.SCALAR ) return old;
      if( old == Type.XSCALAR || old == Type.ANY ) break; // Result is the nt unchanged
      if( !(old instanceof TypeMemPtr) ) {
        if( old instanceof Cyclic && ((Cyclic)old).cyclic() ) bs.clr(nt._uid,old._uid);
        return Type.SCALAR; // Not a TMP
      }
      TypeMemPtr optr = (TypeMemPtr)old;
      nptr._aliases = nptr._aliases.meet(optr._aliases);
      nptr._obj = (TypeStruct)ax_meet(bs,nptr._obj,optr._obj);
      break;
    }
    case TSTRUCT: {
      TypeStruct ots = (TypeStruct)old, nts = (TypeStruct)nt;
      // Meet all the non-recursive parts
      nts._any &= ots._any;
      for( TypeFld ofld : ots ) {
        TypeFld nfld = nts.get(ofld._fld);
        if( nfld == null ) {
          if( nts._any ) nts.add_fld(ofld); // New is high, so gets all the old fields
        } else {
          nfld.cmeet(ofld);     // Meet of non-recursive field parts
        }
      }
      // Remove new fields that are not in old.
      Iter it = nts.iterator();
      while( it.hasNext() )
        if( !ots.has(it.next()._fld) )
          it.remove();
      // Now recursively do all common fields
      for( TypeFld ofld : ots ) {
        TypeFld nfld = nts.get(ofld._fld);
        if( nfld != null && nfld != ofld )
          nfld.setX(ax_meet(bs,nfld._t,ofld._t));
      }
      break;
    }
    default: throw AA.unimpl();
    }
    return nt;
  }

  // -------------------------------------------------------------------------
  // Approximate an otherwise endless unrolled sequence of:
  //    ...TMP[alias] -> Struct -> [FunPtr]* -> TMP[alias] -> Struct -> ...

  // By chopping off the endless tail, and meeting it with SCALAR.

  // This version IS associative with meet: A.apx.B == A.B.apx
  private static final Ary<IHashMap> AXCYCLICS = new Ary<>(IHashMap.class);
  public TypeStruct approx2( int cutoff, BitsAlias aliases ) {
    // Fast-path cutout for boring structs
    boolean shallow=true;
    for( int i=0; i<_flds._len; i++ ) {
      TypeFld fld = _flds._es[i];
      if( fld._t instanceof TypeMemPtr ||
          (fld._t instanceof TypeFunPtr && !((TypeFunPtr)fld._t)._ret.is_simple()) )
        { shallow=false; break; }
    }
    if( shallow ) return this;  // Fast cutout for boring structs
    for( int i=0; i<cutoff; i++ )
      if( i>= AXCYCLICS._len ) AXCYCLICS.push(new IHashMap());
      else AXCYCLICS.at(i).clear();
    Type apx = _apx(cutoff-1,aliases,this);
    apx = apx.install();
    return (TypeStruct)apx;
  }

  // Walk recursively, at cutoff return SCALAR otherwise return self.
  // Clone incrementally, as needed.
  // - If the return is self, then no code-clone happened.
  // - If the return is NOT self, then clone self and return the clone.
  // If cyclic, walk all once looking for a not-self.
  // - If all returns are self, then no code-clone happened.
  // - If even one return is NOT self, then clone self and revisit.
  private static Type _apx( int cutoff, BitsAlias aliases, Type t ) {
    if( !(t instanceof Cyclic) ) return t;
    if( t instanceof TypeMemPtr && aliases.overlaps(((TypeMemPtr)t)._aliases) ) {
      if( cutoff == 0 )
        return Type.SCALAR;     // Cutoff to Scalar
      cutoff--;                 // Lower cutoff
    }
    IHashMap axmap = AXCYCLICS.at(cutoff);
    Type c = axmap.get(t);      // Check for cycles
    if( c!=null ) return c;     // Return prior
    axmap.put(t,c = t.copy());
    //((Cyclic)c).walk_update(fld -> _apx(fcutoff,aliases,fld));
    // Recursively apply
    switch( c._type ) {
    case TMEMPTR: ((TypeMemPtr)c)._obj = (TypeStruct)_apx(cutoff,aliases,((TypeMemPtr)c)._obj ) ; break;
    case TFLD:    ((TypeFld   )c)._t   =             _apx(cutoff,aliases,((TypeFld   )c)._t   ) ; break;
    case TFUNPTR: ((TypeFunPtr)c).set_dsp(           _apx(cutoff,aliases,((TypeFunPtr)c).dsp()));
                  ((TypeFunPtr)c)._ret =             _apx(cutoff,aliases,((TypeFunPtr)c)._ret ) ; break;
    case TSTRUCT: {
      TypeStruct ts = (TypeStruct)c;
      for( int i=0; i<ts._flds._len; i++ ) ts._flds._es[i] = (TypeFld)_apx(cutoff,aliases,ts._flds._es[i]);
      break;
    }
    default: throw unimpl();
    }
    return c;
  }

  // -------------------------------------------------------------------------
  // Build a (recursively) sharpened pointer from memory.  Alias sets can be
  // looked-up directly in a map from BitsAlias to TypeObjs.  This is useful
  // for resolving all the deep pointer structures at a point in the program
  // (i.e., error checking arguments).  Given a TypeMem and a BitsAlias it
  // returns a TypeObj (and extends the HashMap for future calls).  The TypeObj
  // may contain deep pointers to other deep TypeObjs, including cyclic types.
  // This function is monotonic in its arguments.
  static TypeMemPtr sharpen( TypeMem mem, TypeMemPtr dull ) {
    assert dull==dull.simple_ptr() && mem.sharp_get(dull)==null;

    // Pass 1:  fill "dull" cache
    HashMap<BitsAlias,TypeMemPtr> dull_cache = new HashMap<>();
    _dull(mem,dull,dull_cache);

    // Pass 2: Stitch together structs with dull pointers to make a possibly cyclic result.
    TypeMemPtr sharp = _sharp(mem,dull,dull_cache);
    assert sharp.interned() == dull_cache.isEmpty();
    // See if we need to cycle-install any cyclic types
    if( dull_cache.isEmpty() )
      return sharp;
    // On exit, cyclic-intern all cyclic things; remove from dull cache.
    TypeStruct mt = sharp._obj.install();
    sharp = sharp.make_from(mt);
    return mem.sharput(dull,sharp);
  }

  // Pass 1:  fill "dull" cache
  //   Check "dull" & "sharp" cache for hit; if so return.
  //   Walk all aliases;
  //     Get obj from mem; it is "dull".
  //     MEET "dull" objs.
  //   If meet is sharp, put in sharp cache & return.
  //   Put dull ptr to dull meet in dull cache.
  //   Walk dull fields; for all dull TMPs, recurse.
  private static void _dull( TypeMem mem, TypeMemPtr dull, HashMap<BitsAlias,TypeMemPtr> dull_cache ) {
    // Check caches and return
    if( mem.sharp_get(dull) != null ) return;
    if( dull_cache.get(dull._aliases) != null ) return;
    if( dull==TypeMemPtr.NO_DISP || dull==TypeMemPtr.NO_DISP.dual() ) { mem.sharput(dull,dull); return; }
    // Walk and meet "dull" fields; all TMPs will point to ISUSED (hence are dull).
    boolean any = dull._aliases.above_center();
    Type t = any ? ISUSED : UNUSED;
    for( int alias : dull._aliases )
      if( alias != 0 )
        for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) ) {
          TypeStruct x = mem.at(kid);
          t = any ? t.join(x) : t.meet(x);
        }
    TypeMemPtr dptr = dull.make_from((TypeStruct)t);
    if( _is_sharp(t) ) {        // If sharp, install and return
      mem.sharput(dull,dptr);
      return;
    }
    // Install in dull result in dull cache BEFORE recursing.  We might see it
    // again if cyclic types.
    dull_cache.put(dull._aliases,dptr);
    // Visit all dull pointers and recursively collect
    for( TypeFld fld : ((TypeStruct)t) ) {
      Type tt = fld._t;
      if( tt instanceof TypeFunPtr ) tt = ((TypeFunPtr)tt).dsp(); //TODO Handle ret also?
      if( tt instanceof TypeMemPtr )
        _dull(mem,(TypeMemPtr)tt,dull_cache);
    }
  }
  // No dull pointers?
  private static boolean _is_sharp(Type t) {
    if( !(t instanceof TypeStruct) ) return true;
    TypeStruct ts = (TypeStruct)t;
    for( TypeFld fld : ts ) {
      Type tt = fld._t;
      assert fld.interned()==tt.interned();
      if( !tt.interned() ||     // Not interned internal, then this is not finished
          (tt instanceof TypeMemPtr && // Or has internal dull pointers
           ((TypeMemPtr)tt)._obj == ISUSED) )
        return false;
    }
    return true;
  }

  // Pass 2: stitch together structs of dull pointers to make a possibly cyclic type.
  //  Check for hit in sharp cache; if so return it.
  //  Get from dull cache; if not interned, flag as cyclic & return it.
  //  Put not-interned dull clone in dull cache.
  //    Walk all fields.
  //    Copy unless TMP; recurse TMP for field.
  //  If not cyclic, all fields already interned; standard intern, put in sharp; remove dull; & return.
  //  If cyclic, then some field is not interned, put on cyclic list?
  //  Return not-interned value.
  private static @NotNull TypeMemPtr _sharp( TypeMem mem, TypeMemPtr dull, HashMap<BitsAlias,TypeMemPtr> dull_cache ) {
    TypeMemPtr sharp = mem.sharp_get(dull);
    if( sharp != null ) return sharp; // Value returned is sharp and interned
    TypeMemPtr dptr = dull_cache.get(dull._aliases);
    if( !dptr.interned() )      // Closed a cycle
      return dptr; // Not-yet-sharp and not interned; return the work-in-progress
    // Copy, replace dull with not-interned dull clone.  Fields are also cloned, not interned.
    TypeStruct dts2 = dptr._obj._clone().set_hash();
    TypeMemPtr dptr2 = dptr.copy();
    dptr2._obj = dts2;
    dull_cache.put(dull._aliases,dptr2);
    // walk all fields, copy unless TMP.
    for( TypeFld fld : dts2 ) {
      if( fld._t instanceof TypeMemPtr ) // For TMP, recurse on dull pointers.
        fld.setX(_sharp(mem,((TypeMemPtr)fld._t),dull_cache));
      if( fld._t instanceof TypeFunPtr ) {
        TypeFunPtr tf = (TypeFunPtr) fld._t;
        // TODO: Sharpen ret as well
        if( tf.dsp() instanceof TypeMemPtr ) { // Need  a pointer to sharpen
          TypeMemPtr dptr3 = _sharp(mem, (TypeMemPtr) tf.dsp(), dull_cache);
          fld.setX(dptr3.interned()             // Sharp return?
                   ? tf.make_from(dptr3)        // Make sharp TFP field
                   : tf._sharpen_clone(dptr3)); // Make dull  TFP field
        }
      }
      if( fld._t.interned() )
        dts2.put(fld.hashcons_free());
    }
    if( !_is_sharp(dts2) ) return dptr2; // Return the work-in-progress
    // Then copied field types are all sharp and interned.
    // Intern the fields themselves.
    for( TypeFld fld : dts2 )
      if( !fld._t.interned() )
        dts2.put(fld.hashcons_free());
    dull_cache.remove(dull._aliases);// Move the entry from dull cache to sharp cache
    TypeStruct sts = dts2.hashcons_free();
    return mem.sharput(dull,dull.make_from(sts));
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
  // Field by index.  Error if not unique.
  public TypeFld fld_idx( int idx ) {
    TypeFld fld = _flds.atX(idx);
    if( fld==null ) return null;
    assert fld._order==idx || fld._order==TypeFld.oTop || fld._order==TypeFld.oBot;
    return fld;
  }
  public TypeFld fld_idx( int idx, int aidx ) {
    TypeFld fld = _flds.atX(idx);
    if( fld==null ) return null;
    assert fld._order==aidx;
    return fld;
  }

  // Non-allocating iterator; pulls iterators from a pool.  The hard part is
  // telling when an iterator ends early, to avoid leaking.  This is not
  // exactly asserted for, so some leaks may happen.
  @Override public Iter iterator() { return Iter.get(this); }
  private static class Iter implements Iterator<TypeFld> {
    private static final Ary<Iter> POOL = new Ary<>(Iter.class);
    private static int CNT=0; // Number of Iters made, helps to track leaks
    Ary<TypeFld> _flds;
    int _i;
    static Iter get(TypeStruct ts) {
      if( POOL.isEmpty() ) { assert CNT<20; CNT++; new Iter().end(); }
      return POOL.pop().init(ts);
    }
    boolean end() { _i=-99; _flds=null; POOL.push(this); return false; }
    private Iter init(TypeStruct ts) { assert _i==-99; _i=0; _flds=ts._flds; return this; }
    @Override public boolean hasNext() {  assert _i>=0; return _i < _flds._len || end(); }
    @Override public TypeFld next() { return _flds._es[_i++]; }
    @Override public void remove() { throw unimpl(); }
  }

  @Override public void walk1( BiFunction<Type,String,Type> map ) { for( TypeFld fld : this ) map.apply(fld,fld._fld); }
  @Override public void walk_update(    UnaryOperator<Type> map ) { for( int i=0; i<_flds._len; i++ ) _flds._es[i] = (TypeFld)map.apply(_flds._es[i]); }

  static boolean isDigit(char c) { return '0' <= c && c <= '9'; }
  public boolean is_tup() {
    if( len()==0 || (len()==1 && get("^")!=null) ) return true;
    return get("0")!=null && get("0")._order==ARG_IDX;
  }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    // Special shortcut for the all-prims display type
    if( get("pi") != null ) {
      sb.p("MATH");
    } else {
      boolean field_sep=false;
      for( TypeFld fld : is_tup() ? osorted_flds() : asorted_flds() ) {
        if( !debug && Util.eq(fld._fld,"^") ) continue; // Do not print the ever-present display
        fld.str(sb,dups,mem,debug); // Field name, access mod, type
        sb.p(is_tup ? ", " : "; "); // Between fields
        field_sep=true;
      }
      if( field_sep ) sb.unchar().unchar();
    }
    sb.p(!is_tup ? "}" : ")");
    return sb;
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

  // Extend the current struct with a new named field, making a new struct
  public TypeStruct add_tup( Type t, int order ) { return add_fldx(TypeFld.make(TypeFld.TUPS[order],t,Access.Final,order)); }
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
      ts = ts.install();
    return ts;
  }
  @Override Type _unbox() {
    if( Util.eq(_name,"int:") )
      return at("_val");
    TypeStruct ts = WIDEN_HASH.get(_uid);
    if( ts!=null ) { ts._cyclic=true; return ts; }
    RECURSIVE_MEET++;
    ts = malloc(_name,_any);
    WIDEN_HASH.put(_uid,ts);
    for( TypeFld fld : this ) ts.add_fld(fld.malloc_from());
    ts.set_hash();
    for( TypeFld fld : ts ) fld.setX(fld._t._unbox());
    if( --RECURSIVE_MEET == 0 )
      ts = ts.install();
    return ts;
  }

  // Used to detect e.g. immutable or value objects
  public boolean is_all_final_fields() {
    for( TypeFld fld : this )
      if( fld._access != Access.Final )
        return false;
    return true;
  }


  //// True if isBitShape on all bits
  //@Override public byte isBitShape(Type t) {
  //  if( isa(t) ) return 0; // Can choose compatible format
  //  if( t.isa(this) ) return 0; // TODO: really: test same flds, each fld isBitShape
  //  return 99;
  //}
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
      if( fld.intern_lookup()==null )
        return false;
    return true;
  }

}
