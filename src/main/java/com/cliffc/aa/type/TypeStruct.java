package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.*;
import java.util.function.*;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

/** A memory-based collection of named fields.  This is a recursive type,
 *  produced by NewNode and structure or tuple constants.  Fields can be
 *  indexed by field name (which can be a digit string, e.g. tuples), but NOT
 *  by a general number - that's an Array.  Fields can ALSO be accessed by
 *  field order, which happens for function parameters.
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
 *
 *  After computing a possibly-cyclic type (via Meet or from-whole-cloth) we
 *  run a DFA minimization algorithm, then a cycle-aware hash and intern the
 *  the result - possibly returning a previous cycle.
 */
public class TypeStruct extends Type<TypeStruct> implements Cyclic, Iterable<TypeFld> {
  static final HashMap<TPair,TypeStruct> MEETS0 = new HashMap<>();

  private boolean _any;         // True=choice/join/high; False=all/meet/low

  // The fields indexed by field name.  Effectively final.
  private Ary<TypeFld> _flds;

  TypeStruct init( String name, boolean any ) {
    super.init(name);
    _any = any;
    if( _flds==null ) _flds = new Ary<>(TypeFld.class);
    else _flds.clear();         // No leftover fields from pool
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
  @Override long static_hash() {
    long hash = 0;
    for( TypeFld fld : this )
      // Can depend on the field name and access, but NOT the type - because recursion.
      // Same hash independent of field visitation order, because the iterator does
      // not make order guarantees.
      hash ^= fld._fld.hashCode() ^ fld._access.hashCode();
    return Util.mix_hash(super.static_hash() ^ (_any?1023:0),hash);
  }

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
    if( cyclic()==null && t.cyclic()==null ) {
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
  private TypeStruct arg(Type t, int n) { _flds.push(TypeFld.make_arg(t,n)); return this; }
  public static TypeStruct args(Type t1         ) { return _malloc().arg(CTRL,CTL_IDX).arg(ALL,MEM_IDX).arg(t1,DSP_IDX)                .hashcons_free(); }
  public static TypeStruct args(Type t1, Type t2) { return _malloc().arg(CTRL,CTL_IDX).arg(ALL,MEM_IDX).arg(t1,DSP_IDX).arg(t2,ARG_IDX).hashcons_free(); }

  // Used to make a few testing constants
  public static TypeStruct make_test( String fld_name, Type t, Access a ) { return make(TypeFld.make(fld_name,t,a)); }

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
    return TypeStruct.make("",false,TypeFld.make(f1,t1),TypeFld.make(f2,t2));
  }


  // Used to make a few (larger and recursive) testing constants.  Some
  // fields are interned and some are recursive and without a type.
  public static TypeStruct malloc_test( TypeFld... flds ) { return malloc_test("",flds); }
  public static TypeStruct malloc_test( String name, TypeFld... flds ) {
    TypeStruct ts = malloc(name,false);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts;
  }

  public int nargs() { return _flds._len; }

  // The lattice extreme values.

  // Possibly allocated.  No fields specified.  All fields are possible and
  // might be ALL (error).  The worst possible result.
  public static final TypeStruct ISUSED = make("",false);
  // Unused by anybody, perhaps not even allocated.  No fields specified.
  // All fields are available as ANY.
  public static final TypeStruct UNUSED = ISUSED.dual();

  // Wrapped primitive prototypes
  public static final TypeStruct INT = TypeStruct.make("int:",false,TypeFld.make("x",TypeInt.INT64));
  public static final TypeStruct FLT = TypeStruct.make("flt:",false,TypeFld.make("x",TypeFlt.FLT64));
  
  // A bunch of types for tests
  public  static final TypeStruct POINT = args(TypeFlt.FLT64,TypeFlt.FLT64);
  public  static final TypeStruct NAMEPT= POINT.set_name("Point:");
  public  static final TypeStruct A     = make_test("a",TypeFlt.FLT64,Access.Final);
  private static final TypeStruct C0    = make_test("c",TypeInt.FALSE,Access.Final); // @{c:0}
  private static final TypeStruct D1    = make_test("d",TypeInt.TRUE ,Access.Final); // @{d:1}
  public  static final TypeStruct ARW   = make_test("a",TypeFlt.FLT64,Access.RW   );
  public  static final TypeStruct EMPTY = make();
  public  static final TypeStruct FLT64 = args(FLT);     // { flt -> }
  public  static final TypeStruct INT64 = args(INT);     // { int -> }
  public  static final TypeStruct SCALAR1=args(SCALAR);            // { scalar -> }
  public  static final TypeStruct INT64_INT64= args(INT,INT); // { int int -> }
  public  static final TypeStruct INT64_FLT64= args(INT,FLT); // { int flt -> }
  public  static final TypeStruct FLT64_INT64= args(FLT,INT); // { flt int -> }
  public  static final TypeStruct FLT64_FLT64= args(FLT,FLT); // { flt flt -> }

  // Pile of sample structs for testing
  static final TypeStruct[] TYPES = new TypeStruct[]{ISUSED,POINT,NAMEPT,A,C0,D1,ARW,INT64_INT64,SCALAR1};

  // Dual the flds, dual the tuple.  Return a not-interned thing.
  @Override protected TypeStruct xdual() {
    TypeStruct ts = malloc(_name,!_any);
    for( TypeFld fld : this ) ts._flds.push(fld.dual());
    return ts;
  }

  // Recursive dual
  @Override void rdual() {
    for( int i=0; i<_flds._len; i++ )
      _dual._flds.set(i,_flds.at(i)._dual);
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
    if( cyclic()!=null && that.cyclic()!=null )
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
    @Override public int hashCode() { return (int)((Util.rot(_ts0.static_hash(),17)) ^ _ts1.static_hash()); }
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
  // Field type byte name.  NPE if field-not-found
  public Type at( String name ) { return get(name)._t; }

  // Field by index, null after end
  public TypeFld get( int idx ) { return _flds.atX(idx); }
  // Field type by index, AIOOBE if field not found
  public Type at( int idx ) { return _flds.at(idx)._t; }

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

  @Override public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) {
    TypeMemPtr rez=null;
    for( TypeFld fld : this ) {
      TypeMemPtr rez2 = map.map(fld,fld._fld);
      rez = rez==null ? rez2 : reduce.apply(rez,rez2);
    }
    return rez;
  }
  @Override public long lwalk( LongStringFunc map, LongOp reduce ) {
    long rez=0xdeadbeefcafebabeL;
    for( TypeFld fld : this )
      rez = reduce.run(rez,map.run(fld,fld._fld));
    return rez;
  }

  @Override public void walk( TypeStrRun map ) {
    for( TypeFld fld : this )
      map.run(fld,fld._fld);
  }
  @Override public void walk_update( TypeMap map ) {
    for( int i=0; i<_flds._len; i++ )
      _flds._es[i] = (TypeFld)map.map(_flds._es[i]);
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
    return get("0")!=null;
  }

  @Override void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"S"+(char)('A'+ucnt._ts++));
      return;
    }
    for( int i=0; i<len(); i++ ) // DO NOT USE iter syntax, else toString fails when the iter pool exhausts during a debug session
      if( get(i)!=null )
        get(i)._str_dups(visit,dups,ucnt);
  }

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
          fld = TypeFld.valueOfArg(P, fid);
          if( fld==null ) aidx++; // Parse "(int64)" correct; tuple with leading id not field name
        }
        if( fld==null )         // Parse a field
          fld = is_tup ? TypeFld.valueOfTup(P,fid,aidx) : TypeFld.valueOfArg(P,fid);

        if( fid!=null ) --RECURSIVE_MEET; // End cyclic field type
        TypeFld ofld = fld;
        fld = P.cyc(fld);                 // Install as needed
        if( fid!=null && fld!=ofld )
          P._dups.put(fid,fld); // Update dups if we early-interned
      } else {                  // Hit a duplicate
        // Ambiguous with un-named tuple fields
        fld = dup instanceof TypeFld dup2 ? dup2
          : TypeFld.malloc(TypeFld.TUPS[aidx==DSP_IDX ? ARG_IDX : aidx],dup,Access.Final);
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
    TypeStruct ts = malloc(_name,_any);
    for( int i=0; i<_flds._len; i++ ) {
      String fname = get(i)._fld;
      ts._flds.push(TypeFld.make(fname,Util.eq(fname,name) ? live : XSCALAR, Access.bot()));
    }
    return ts.hashcons_free();
  }

  // Keep field names and orders.  Widen all field contents, including finals.
  // Handles cycles
  @Override TypeStruct _widen() {
    TypeStruct ts = WIDEN_HASH.get(_uid);
    if( ts!=null ) throw unimpl(); // { ts.set_cyclic(); return ts; }
    RECURSIVE_MEET++;
    ts = malloc(_name,_any);
    WIDEN_HASH.put(_uid,ts);
    for( TypeFld fld : this ) ts.add_fld(fld.malloc_from());
    for( TypeFld fld : ts ) fld.setX(fld._t._widen());
    if( --RECURSIVE_MEET == 0 )
      ts = Cyclic.install(ts);
    return ts;
  }

  @Override public boolean above_center() { return _any; }
  @Override public boolean is_con() {
    for( int i=0; i<_flds._len; i++ )
      if( !_flds._es[i].is_con() )
        return false;
    return true;    
  }
  @Override public Type meet_nil(Type nil) { return this; }

  @Override boolean contains( Type t, VBitSet bs ) {
    if( bs==null ) bs=new VBitSet();
    if( bs.tset(_uid) ) return false;
    for( TypeFld fld : this ) if( fld._t==t || fld._t.contains(t,bs) ) return true;
    return false;
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
