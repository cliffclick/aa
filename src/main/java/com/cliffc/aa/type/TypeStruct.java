package com.cliffc.aa.type;

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
  // Cyclic (complex/slow) interning
  public TypeStruct install() { return Cyclic.install(this); }

  // Approximate an otherwise endless unrolled sequence of:
  //    ...TMP[alias] -> Struct -> [FunPtr]* -> TMP[alias] -> Struct -> ...
  //
  // We can get endless type growth with recursive types and recursive
  // functions.  Not morally equivalent to HotSpot int-range 'widening', which
  // specifically widens at each Loop Phi, and limits the number of widenings.
  // Here we get 'widened' at each HM application of class Struct, or at each
  // Lambda.arg_meet.
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
  public TypeStruct approx( int cutoff, BitsAlias aliases ) { return approx2(aliases); }

  /**
  Simply meeting a lower [12] over an upper [12] is not sufficient.  Since the
  lower [12] also includes a 'succ=scalar' the PATH .succ.pred.succ is Scalar.
  That same path going down and going to the right has to monotonically fall.

  [12]@{                               [12]@{
    vpred=~scalar                         pred=~scalar
    nsucc= *[12]@{     >>> ISA >>>        succ= scalar // Succ field falls
      vpred=*[12]@{ nsucc=scalar }       }
    }
  }
  .succ.pred.succ=scalar               .succ[.pred.succ] = scalar

  --- approx ---                       --- approx ---
  [12]@{                               [12]@{
    pred= $recursive$  >>> NOT ISA >>>   pred=~scalar
    succ= $recursive$                    succ= scalar
  }                                    }
  .succ.pred.succ=[12]...              .succ[.pred.succ] = scalar
    and this path LIFTS.
  */

  // -------------------------------------------------------------------------
  // Approximate an otherwise endless unrolled sequence of:
  //    ...TMP[alias] -> Struct -> [FunPtr]* -> TMP[alias] -> Struct -> ...

  public TypeStruct approx2( BitsAlias aliases ) {
    //// Fast-path cutout for boring structs
    //boolean shallow=true;
    //for( int i=0; i<_flds._len; i++ ) {
    //  TypeFld fld = _flds._es[i];
    //  if( fld._t instanceof TypeMemPtr ||
    //      (fld._t instanceof TypeFunPtr tfp && !tfp._ret.is_simple()) )
    //    { shallow=false; break; }
    //}
    //if( shallow ) return this; // Fast cutout for boring structs
    TypeStruct ts=this;
    while(true) {
      assert RECURSIVE_MEET==0;
      assert MEETS0.isEmpty() && AXOLD2NEW.isEmpty() && AXVISIT.size()==0 && AXMEET.isEmpty();
      AXALIAS = aliases;
      TypeMemPtr ptmp = TypeMemPtr.make(aliases,ts), ax_chk;
      TypeMemPtr ctmp = (TypeMemPtr)_apx2(ptmp,null,null,0);

      TypeStruct apx = ctmp._obj;
      assert AXMEET.isEmpty();
      MEETS0.clear();  AXOLD2NEW.clear(true);  AXVISIT.clear();
      apx = apx.install();
      assert ts.isa(apx);       // Self monotonic
      ctmp = TypeMemPtr.make(aliases,apx);
      ax_chk=_ax_chk(new VBitSet(),ctmp,null,aliases);
      if( ax_chk==null ) return apx;
      ts = apx;
    }
  }

  // Read the old Type and clone into a new Type.  Along the way look for
  // overlapping instances of AXALIAS.  If the new deep overlap point ISA the
  // old shallow overlap point, make a closed cycle in the new clone.
  // Otherwise, MEET the prior shallow overlap point into the new deep point, in
  // addition to the cloning.  Handle cycles in the old code (by stopping
  // cloning).  As part of a normal MEET-into, if the new code ISA a high type,
  // the old code will effectively be cloned.
  //
  // As a result of this step, all AXALIAS instances will be ISA the prior
  // shallower AXALIAS instance (Types go downhill the deeper into the
  // structure we go).
  //
  // Passed in an old Type to clone, an old prior alias point, and a safety
  // depth.  Also passed as globals are a map from old to new and the overlap
  // alias.  The mapping 'unwinds' as the recursion unwinds, because the same
  // old Type might be visited several times making unique new instances of new
  // Types and the mapping is used both to catch cycles and to find the
  // matching new Type (on this instance of walking old).

  private static final BitSetSparse AXVISIT = new BitSetSparse();
  private static final NonBlockingHashMapLong<Type> AXOLD2NEW = new NonBlockingHashMapLong<>();
  private static final Ary<Type> AXMEET = new Ary<>(Type.class);
  private static BitsAlias AXALIAS;
  private static Type _apx2( Type old, TypeMemPtr pax, TypeMemPtr nax, final int depth ) {
    assert depth<100;  // Stop stack overflow early, much easier debugging

    if( !(old instanceof Cyclic) ) return old;

    TypeMemPtr tmp = old instanceof TypeMemPtr tmp2 && AXALIAS.overlaps(tmp2._aliases) ? tmp2 : null;
    if( pax!=null && tmp!=null ) {
      Type mt = tmp.meet(pax);
      if( mt==pax/*tmp.isa.pax*/ ) return nax; // Push new version of pax, no need to meet-over since ISA means no progress
      if( mt!=tmp/*pax.isa.tmp*/ ) // Missing invariant
        old = mt; // Force invariant in old-side before walking
    }
    // todo: must clone TS to avoid infinite loops on TMP+TS with unrelated alias
    // todo: otherwise must PEEL TS because reached with a TMP with related alias plus random other aliases
    // so probabaly need to pass a prior alias along in the recursion, or a boolean tmp==null
    if( old instanceof TypeMemPtr ) {
      Type nnn = AXOLD2NEW.get(old._uid);
      if( nnn!=null ) return nnn; // Dup check: been here, done that.
    }
    // Clone
    Type fnnn = old.copy();
    if( old instanceof TypeMemPtr )
      AXOLD2NEW.put(old._uid, fnnn );  // Make a copy; copy is NOT interned and IS in the dup check.

    // Recurse; If new overlap point swap pax/nax
    ((Cyclic)fnnn).walk_update(fld -> _apx2(fld,
                                            tmp==null ? pax : tmp,
                                            tmp==null ? nax : (TypeMemPtr)fnnn,depth+1));
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
    if( !(t instanceof TypeStruct ts) ) return true;
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
      if( fld._t instanceof TypeFunPtr tf ) {
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
  @Override public Type walk_apx(int cutoff, NonBlockingHashMapLong<Integer> depth) {
    throw unimpl();
  }
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
    return get("0")!=null && get("0")._order==ARG_IDX;
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
      for( TypeFld fld : indent ? _flds : (is_tup() ? osorted_flds() : asorted_flds()) ) {
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
      ts = ts.install();
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
      if( fld.intern_lookup()==null )
        return false;
    return true;
  }
}
