package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;

import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

/** A memory-based collection of optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.  Fields
 *  can be indexed by field name or numeric constant (i.e. tuples), but NOT by
 *  a general number - thats an Array.  Fields are matched on name and not
 *  index; field order is irrevelant to named fields.
 *
 *  Structs can be open or closed (and like all Types, high or low).  An open
 *  struct acts as-if it has an all possible field names (except those
 *  explicitly mentioned) set to SCALAR or XSCALAR.  Adding a new SCALAR field
 *  to an open low struct is a no-op, since such a field already implicitly
 *  exists.
 *
 *  The recursive type poses some interesting challenges.  It is represented as
 *  literally a cycle of pointers which must include a TypeStruct (and not a
 *  TypeTuple which only roots Types), a TypeMemPtr (edge) or a TypeFunPtr
 *  (display pointer) and a TypeFld.  Type inference involves finding the Meet
 *  of two cyclic structures.  The cycles will not generally be of the same
 *  length.  However, each field Meets independently (and fields in one
 *  structure but not the other are not in the final Meet).  This means we are
 *  NOT trying to solve the general problem of graph-equivalence (a known NP
 *  hard problem).  Instead we can solve each field independently and also
 *  intersect across common fields.
 *
 *  When solving across a single field, we will find some prefix and then
 *  possibly a cycle - conceptually the type unrolls forever.  When doing the
 *  Meet we conceptually unroll both types forever, compute the Meet element by
 *  element... but when both types have looped, we can stop and the discovered
 *  cycle is the Meet's cycle.
 */
public class TypeStruct extends TypeObj<TypeStruct> {
  public boolean _open;   // Extra fields are treated as ALL (or ANY)
  public boolean _cyclic; // Type is cyclic.  This is a summary property, not a part of the type, hence is not in the equals nor hash
  // The fields indexed by field name.  Effectively final.  Public iterator, but private.
  private final IdentityHashMap<String,TypeFld> _flds = new IdentityHashMap<>();

  private TypeStruct init( String name, boolean any, boolean open ) {
    super.init(TSTRUCT, name, any, any);
    _open  = open;
    _hash = 0;                  // No hash, as fields are changing
    _flds.clear();              // No leftover fields from pool
    return this;
  }

  // Hash code computation.
  // Fairly subtle, because the typical hash code is built up from the hashes of
  // its parts, but the parts are not available during construction of a cyclic type.
  // We can count on the field names and accesses but not field order, nor field type.
  @Override public int compute_hash() {
    int hash = super.compute_hash() +(_open?1023:0);
    for( TypeFld fld : _flds.values() )
      // Can depend on the field name and access, but NOT the type - because recursion
      hash ^= (fld._fld.hashCode() + fld._access.hashCode());
    if( hash==0 ) hash = super.compute_hash();
    return hash;
  }

  // Returns 1 for definitely equals, 0 for definitely unequals, and -1 if
  // needing the cyclic test.
  private int cmp( TypeStruct t ) {
    assert _hash!=0 && t._hash!=0; // Not comparable until both are hashable
    if( !super.equals(t) ) return 0;
    if( _flds.size() != t._flds.size() || _open != t._open ) return 0;
    // All fields must be equals
    for( TypeFld fld : _flds.values() ) {
      TypeFld fld2 = t._flds.get(fld._fld);
      if( fld2==null ) return 0; // Missing field name
      int cmp = fld.cmp(fld2);
      if( cmp!= 1 ) return cmp; // Fields do not match, or needs a cyclic check
    }
    return 1;                   // Everything is equals, right now
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    // While we would like to use the notion of interned Type[] during the
    // normal Type.INTERN check, we also get here during building of cyclic
    // structures for which we'll fall into the cyclic check - as the Type[]s
    // are not interned yet.
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
    TypeStruct t2 = find_other();
    if( t2 !=null ) return t2==t   ; // Already in cycle report equals or not
    TypeStruct t3 = t.find_other();
    if( t3 !=null ) return t3==this;// Already in cycle report equals or not
    int x = cmp(t);
    if( x != -1 ) return x == 1;

    int len = CYCLES._len;
    CYCLES.add(this).add(t);
    boolean eq=cycle_equals0(t);
    assert CYCLES._len==len+2;
    CYCLES._len=len;
    return eq;
  }
  private boolean cycle_equals0( TypeStruct t ) {
    // TODO: might get here with more unrelated structs, so need to check eg access, and missing names
    assert _flds.size()==t._flds.size();
    for( TypeFld fld : _flds.values() ) {
      TypeFld fld1 = t._flds.get(fld._fld);
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

  static boolean isDigit(char c) { return '0' <= c && c <= '9'; }
  private boolean is_tup() {
    if( _flds.size()<=1 ) return true;
    return _flds.get("0")!=null && _flds.get("0")._order==ARG_IDX;
  }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    // Special shortcut for the all-prims display type
    TypeFld bfld;
    if( (bfld=fld_find("!")) != null && fld_find("math_pi") != null ) {
      Type t1 = bfld._t;
      sb.p(t1 instanceof TypeFunPtr
           ? (((TypeFunPtr)t1)._fidxs.above_center() ? "PRIMS" : "LOW_PRIMS")
           : "PRIMS_"+t1);
    } else {
      boolean field_sep=false;
      for( TypeFld fld : is_tup() ? osorted_flds() : asorted_flds() ) {
        if( !debug && Util.eq(fld._fld,"^") ) continue; // Do not print the ever-present display
        fld.str(sb,dups,mem,debug); // Field name, access mod, type
        sb.p(is_tup ? ", " : "; "); // Between fields
        field_sep=true;
      }
      if( _open ) sb.p("...");    // More fields allowed
      else if( field_sep ) sb.unchar().unchar();
    }
    sb.p(!is_tup ? "}" : ")");
    return sb;
  }

  // Unlike other types, TypeStruct might make cyclic types for which a
  // DAG-like bottom-up-remove-dups approach cannot work.
  static { new Pool(TSTRUCT,new TypeStruct()); }
  public static TypeStruct malloc( String name, boolean any, boolean open ) {
    return POOLS[TSTRUCT].<TypeStruct>malloc().init(name,any,open);
  }
  public TypeStruct hashcons_free() {
    // All subparts already interned
    if( RECURSIVE_MEET ==0 ) for( TypeFld fld : _flds.values() ) assert fld.interned();
    return super.hashcons_free();
  }

  // Make a collection of fields, with no display and all with default names and final fields.
  private static TypeStruct make0() { return malloc("",false,false); }
  private TypeStruct add_arg(Type t, int n) { return add_fld(TypeFld.make_arg(t,n)); }
  public static TypeStruct args(Type t1         ) { return make0().add_arg(t1,ARG_IDX)                      .hashcons_free(); }
  public static TypeStruct args(Type t1, Type t2) { return make0().add_arg(t1,ARG_IDX).add_arg(t2,ARG_IDX+1).hashcons_free(); }
  // Used by tests only, so ... is ok.
  public static TypeStruct tups(Type... ts ) {
    TypeStruct st = make0();
    for( int i=0; i<ts.length; i++ )
      st.add_fld(TypeFld.make_tup(ts[i],ARG_IDX+i));
    return st.hashcons_free();
  }
  public static TypeStruct tupsD(Type... ts ) {
    TypeStruct st = make0();
    st.add_fld(TypeFld.NO_DISP);
    for( int i=0; i<ts.length; i++ )
      st.add_fld(TypeFld.make_tup(ts[i],ARG_IDX+i));
    return st.hashcons_free();
  }

  // Arys are used by the parser
  public static TypeStruct make( String name, boolean any, boolean open, Ary<TypeFld> flds ) {
    TypeStruct ts = malloc(name,any,open);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts.hashcons_free();
  }
  // Used to make a few testing constants
  public static TypeStruct make( String fld_name, Type t, Access a ) { return make(TypeFld.make(fld_name,t,a,ARG_IDX)); }
  // Used to make a few (larger and recursive) testing constants.  Some of the
  // fields are interned and some are recursive and without a type.
  public static TypeStruct malloc( String name, boolean any, boolean open, TypeFld... flds ) {
    TypeStruct ts = malloc(name,any,open);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts;
  }

  // Make using the fields, with no struct name, low and closed; typical for a
  // well-known structure.  Might auto-allocate a TypeFld[] - which is a
  // perf-hit in high usage points.  Typically used this way in tests.
  public static TypeStruct make( TypeFld... flds ) { return make("",false,false,flds); }
  public static TypeStruct make( String name, boolean any, boolean open, TypeFld... flds ) {
    TypeStruct ts = malloc(name,any,open);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts.hashcons_free();
  }
  // Without NO_DISP
  public static TypeStruct make2flds( String f1, Type t1, String f2, Type t2 ) {
    return make("",false,false,TypeFld.make(f1,t1,ARG_IDX),TypeFld.make(f2,t2,ARG_IDX+1));
  }
  // With NO_DISP
  public static TypeStruct make2fldsD( String f1, Type t1, String f2, Type t2 ) {
    return make("",false,false,TypeFld.NO_DISP,TypeFld.make(f1,t1,ARG_IDX),TypeFld.make(f2,t2,ARG_IDX+1));
  }

  // Add fields from a Type[].  Will auto-allocate the Type[], if not already
  // allocated - which is a perf-hit in high usage points.  Typically used this
  // way in tests.
  public static TypeStruct maket( Type... ts ) { return make("",false,false,ts); }
  public static TypeStruct make( String name, boolean any, boolean open, Type... ts ) {
    TypeStruct st = malloc(name,any,open);
    st.add_fld(TypeFld.NO_DISP);
    for( int i=0; i<ts.length; i++ )
      st.add_fld(TypeFld.make_tup(ts[i],ARG_IDX+i));
    return st.hashcons_free();
  }

  // Keep the fields but change name,any,open
  public TypeStruct make_from(String name, boolean any, boolean open ) {
    assert interned();
    TypeStruct ts = malloc(name,any,open);
    for( TypeFld fld : _flds.values() ) ts.add_fld(fld);
    return ts.hashcons_free();
  }
  // Keep the name,any,open but change the fields
  public TypeStruct make_from(TypeStruct ts ) {
    assert interned() && ts.interned();
    TypeStruct st = malloc(_name,_any,_open);
    for( TypeFld fld : ts.flds() ) st.add_fld(fld);
    return st.hashcons_free();
  }
  // Make a named TypeStruct from an unnamed one
  public TypeStruct make_from( String name ) { return make_from(name,_any,_open);  }
  // Used by NewObj
  public TypeStruct make_from( Ary<TypeFld> flds ) {
    TypeStruct ts = malloc(_name,_any,_open);
    for( TypeFld fld : flds ) ts.add_fld(fld);
    return ts.hashcons_free();
  }


  // Make an "open" struct with an initial display field.
  public static TypeStruct open(Type tdisp) { return make("",false,true,TypeFld.make_arg(tdisp,DSP_IDX)); }
  // Make a closed struct from an open one
  public TypeStruct close() { assert _open; return make_from(_name,_any,false); } // Mark as no-more-fields

  // Add a field to an open, under construction TypeStruct
  public TypeStruct add_fld( TypeFld fld ) {
    TypeFld old = _flds.put(fld._fld,fld);
    assert old==null && _hash==0; // No accidental replacing
    return this;
  }
  // Set/replace a field to an open, under construction TypeStruct
  public TypeStruct set_fld( TypeFld fld ) {
    TypeFld old = _flds.put(fld._fld,fld);
    assert !interned() && old!=null; // No accidental adding
    return this;
  }


  @Override boolean is_display() {
    TypeFld disp;
    return
      this==TypeMemPtr.DISPLAY || this==TypeMemPtr.DISPLAY._dual ||
      ((disp=_flds.get("^"))!=null && disp.is_display_ptr());
  }

  // The lattice extreme values
  public  static final TypeStruct ANYSTRUCT = make("",true ,false);
  public  static final TypeStruct ALLSTRUCT = make("",false,true );

  // A bunch of types for tests
  public  static final TypeStruct POINT = args(TypeFlt.FLT64,TypeFlt.FLT64);
  public  static final TypeStruct NAMEPT= POINT.make_from("Point:",false,false);
  public  static final TypeStruct A     = make("a",TypeFlt.FLT64,Access.Final);
  private static final TypeStruct C0    = make("c",TypeInt.FALSE,Access.Final); // @{c:0}
  private static final TypeStruct D1    = make("d",TypeInt.TRUE ,Access.Final); // @{d:1}
  public  static final TypeStruct ARW   = make("a",TypeFlt.FLT64,Access.RW   );
  public  static final TypeStruct EMPTY = make0().hashcons_free();
  public  static final TypeStruct FLT64 = args(TypeFlt.FLT64);     // { flt -> }
  public  static final TypeStruct INT64 = args(TypeInt.INT64);     // { int -> }
  public  static final TypeStruct SCALAR1=args(SCALAR);            // { scalar -> }
  public  static final TypeStruct INT64_INT64= args(TypeInt.INT64,TypeInt.INT64); // { int int -> }
  public  static final TypeStruct FLT64_FLT64= args(TypeFlt.FLT64,TypeFlt.FLT64); // { flt flt -> }

  // Pile of sample structs for testing
  static final TypeStruct[] TYPES = new TypeStruct[]{ALLSTRUCT,POINT,NAMEPT,A,C0,D1,ARW,INT64_INT64,SCALAR1};

  // Dual the flds, dual the tuple.  Return a not-interned thing.
  @Override protected TypeStruct xdual() {
    TypeStruct ts = malloc(_name,!_any,!_open);
    for( TypeFld fld : _flds.values() ) ts.add_fld(fld.dual());
    return ts;
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    assert _hash == compute_hash();
    if( _dual != null ) return _dual;
    assert !interned();
    TypeStruct dual = _dual = malloc(_name,!_any,!_open);
    dual._dual = this;          // Stop the recursion
    dual._cyclic = _cyclic;     // Only here for recursive structs
    // Have to add the fields first, then set the hash, then loop over the fields recursing.
    for( TypeFld fld : _flds.values() )
      // Some fields are interned already, the cyclic ones are not.
      dual.add_fld(fld.interned() ? fld._dual : fld.xdual());
    dual._hash = dual.compute_hash();
    for( TypeFld fld : _flds.values() )
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
    case TLIVE:
    case TSTR:   return OBJ;
    case TOBJ:   return t.xmeet(this);
    case TFUNSIG:
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
    TypeStruct ts = malloc("",_any&that._any,_open|that._open);
    // Fields in both
    for( TypeFld fld : _flds.values() ) {
      TypeFld tfld = that._flds.get(fld._fld);
      if( tfld != null ) ts.add_fld(cyclic ? TypeFld.cmeet(fld,tfld) : fld.xmeet(tfld));
    }
    // Fields in LHS, and RHS is high (can extend with LHS fields)
    if( that._any )
      for( TypeFld fld : _flds.values() )
        if( !that._flds.containsKey(fld._fld) )
          ts.add_fld(fld); // Only in LHS and RHS is a high field
    // Fields in RHS, and LHS is high (can extend with RHS fields)
    if( _any )
      for( TypeFld fld : that._flds.values() )
        if( !_flds.containsKey(fld._fld) )
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
    for( TypeFld fld : mt.flds() ) {
      TypeFld lff = this.fld_find(fld._fld);
      TypeFld rtf = that.fld_find(fld._fld);
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

    // Remove any final UF before installation.
    // Do not install until the cycle is complete.
    RECURSIVE_MEET++;
    mt = mt.shrink();
    Ary<Type> reaches = mt.reachable(); // Recompute reaches after shrink
    assert check_uf(reaches);
    UF.clear();
    RECURSIVE_MEET--;
    // This completes 'mt' as the Meet structure.
    return mt.install_cyclic(reaches);
  }

  // Test entry point.  The struct is part of a single SCC (not a DAG of
  // connected SCCs), and some parts are not hashed.
  public TypeStruct install() {
    RECURSIVE_MEET++;
    TypeStruct mt = shrink();
    Ary<Type> reaches = mt.reachable(); // Recompute reaches after shrink
    assert check_uf(reaches);
    UF.clear();
    RECURSIVE_MEET--;
    return mt.install_cyclic(reaches);
  }

  // other places all call shrink / check_uf / UF.clear / etc.
  // Boilerplate the other stuff.

  // Install, cleanup and return
  TypeStruct install_cyclic(Ary<Type> reachs) {
    // Walk all, set cycle bits and hashes
    get_cyclic();
    // Check for dups.  If found, delete entire cycle, and return original.
    TypeStruct old = (TypeStruct)intern_lookup();
    if( old == null ) {         // Not a dup
      for( Type t : reachs )
        assert t.intern_lookup()==null && t._hash==t.compute_hash() && t._dual==null;
      rdual();               // Complete cyclic dual
      // Insert all members of the cycle into the hashcons.  If self-symmetric,
      // also replace entire cycle with self at each point.
      for( Type t : reachs )
        if( t.retern() != t._dual ) t._dual.retern();
      old = this;
    }
    MEETS0.clear();
    return old;
  }

  // Shallow clone, not interned.  Fields are also cloned, but not deeper.
  private TypeStruct _clone() {
    assert interned();
    TypeStruct ts = malloc(_name,_any,_open);
    for( TypeFld fld : _flds.values() )
      ts.add_fld(fld.malloc_from()); // Shallow field clone
    return ts;
  }
  // Shallow clone, not interned.  Fields are referenced, not cloned
  @Override TypeStruct copy() {
    POOLS[_type]._clone++;
    TypeStruct ts = new TypeStruct().init(_name,_any,_open);
    for( TypeFld fld : _flds.values() ) ts.add_fld(fld);
    return ts;
  }

  // This is for a struct that has grown 'too deep', and needs to be
  // approximated to avoid infinite growth.
  public  static final NonBlockingHashMapLong<Type> UF = new NonBlockingHashMapLong<>();
  private static final IHashMap OLD2APX = new IHashMap();
  public TypeStruct approx( int cutoff, int alias ) {
    boolean shallow=true;
    for( TypeFld fld : _flds.values() )
      if( fld._t._type == TMEMPTR ) { shallow=false; break; }
    if( shallow ) return this;  // Fast cutout for boring structs

    // Scan the old copy for elements that are too deep.
    // 'Meet' those into the clone at one layer up.
    RECURSIVE_MEET++;
    assert UF.isEmpty();
    assert OLD2APX.isEmpty();
    TypeStruct apx = ax_impl_struct( alias, true, cutoff, null, 0, this, this );
    // Remove any leftover internal duplication
    apx = apx.shrink();
    RECURSIVE_MEET--;
    TypeStruct rez = this;
    if( apx != this ) {
      Ary<Type> reaches = apx.reachable();
      assert check_uf(reaches);
      assert !check_interned(reaches); // Stronger than check_uf: nothing is interned
      rez = apx.install_cyclic(reaches);
      assert this.isa(rez);
    }
    UF.clear();
    OLD2APX.clear();
    return rez;
  }

  // Make a new TypeStruct which is the merge of the original TypeStruct with
  // the too-deep parts merged into shallower parts.
  private static TypeStruct ax_impl_struct( int alias, boolean isnews, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeStruct old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeStruct nt = OLD2APX.get(old);
    if( nt != null ) return ufind(nt);

    if( isnews ) {            // Depth-increasing struct?
      if( d==cutoff ) {       // Cannot increase depth any more
        cutoffs.push(old);    // Save cutoff point for later MEET
        return OLD2APX.get(dold); // Return last valid depth - forces cycle
      } else {
        assert cutoffs == null; // Approaching max depth, make a place to record cutoffs
        if( d+1==cutoff ) cutoffs = new Ary<>(TypeStruct.class);
      }
      d++;              // Increase depth
      dold = old;       // And this is the last TypeStruct seen at this depth
    }
    // Clone the old, to make the approximation into
    TypeStruct nts = old._clone();
    OLD2APX.put(old,nts);
    for( TypeFld fld : old.flds() ) {
      Type t = fld._t;
      if( t instanceof TypeMemPtr )
        nts.fld_find(fld._fld).setX(ax_impl_ptr (alias,cutoff,cutoffs,d,dold,(TypeMemPtr)t));
      else if( t instanceof TypeFunPtr )
        nts.fld_find(fld._fld).setX(ax_impl_fptr(alias,cutoff,cutoffs,d,dold,(TypeFunPtr)t));
    }
    if( isnews && d==cutoff ) {
      while( !cutoffs.isEmpty() ) { // At depth limit, meet with cutoff to make the approximation
        Type mt = ax_meet(new BitSetSparse(), nts,cutoffs.pop());
        assert mt==nts;
      }
    }
    OLD2APX.put(old,null); // Do not keep sharing the "tails"
    return nts;
  }

  private static TypeMemPtr ax_impl_ptr( int alias, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeMemPtr old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeMemPtr nt = OLD2APX.get(old);
    if( nt != null ) return ufind(nt);

    // Walk internal structure, meeting into the approximation
    TypeMemPtr nmp = old.copy();
    OLD2APX.put(old,nmp);
    if( old._obj instanceof TypeStruct )
      nmp._obj = ax_impl_struct(alias,nmp._aliases.test(alias),cutoff,cutoffs,d,dold,(TypeStruct)old._obj);
    else if( old._obj == TypeObj.XOBJ || old._obj==nmp._obj )
      ; // No change to nmp._obj
    else if( old._obj == TypeObj.OBJ )
      nmp._obj = TypeObj.OBJ;   // Falls hard
    else
      throw unimpl();
    OLD2APX.put(old,null);      // Do not keep sharing the "tails"
    return nmp;
  }
  private static Type ax_impl_fptr( int alias, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeFunPtr old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeFunPtr nt = OLD2APX.get(old);
    if( nt != null ) return ufind(nt);
    if( old._disp==Type.ANY )
       return old; // no ufind because its old

    // Walk internal structure, meeting into the approximation
    TypeFunPtr nmp = old.copy();
    OLD2APX.put(old,nmp);
    nmp._disp = ax_impl_ptr(alias,cutoff,cutoffs,d,dold,(TypeMemPtr)old._disp);
    OLD2APX.put(old,null);      // Do not keep sharing the "tails"
    return nmp;
  }

  // Update-in-place 'meet' of pre-allocated new types.  Walk all the old type
  // and meet into the corresponding new type.  Changes the internal edges of
  // the new types, so their hash remains undefined.
  private static Type ax_meet( BitSetSparse bs, Type nt, Type old ) {
    assert old.interned();
    if( nt.interned() ) return nt.meet(old);
    assert nt._hash==0;         // Not definable yet, as nt may yet pick up fields
    nt = ufind(nt);
    if( nt == old ) return old;
    if( bs.tset(nt._uid,old._uid) ) return nt; // Been there, done that

    // TODO: Make a non-recursive "meet into".
    // Meet old into nt
    switch( nt._type ) {
    case TSCALAR: break; // Nothing to meet
    case TFUNPTR: {
      TypeFunPtr nptr = (TypeFunPtr)nt;
      if( old == Type.NIL || old == Type.XNIL ) return nptr.ax_meet_nil(old);
      if( old == Type.SCALAR )
        return union(nt,old); // Result is a scalar, which changes the structure of the new types.
      if( old == Type.XSCALAR ) break; // Result is the nt unchanged
      if( !(old instanceof TypeFunPtr) ) throw AA.unimpl(); // Not a xscalar, not a funptr, probably falls to scalar
      TypeFunPtr optr = (TypeFunPtr)old;
      nptr._fidxs = nptr._fidxs.meet(optr._fidxs);
      // While structs normally meet, function args *join*, although the return still meets.
      nptr._disp = ax_meet(bs,nptr._disp,optr._disp);
      break;
    }
    case TMEMPTR: {
      TypeMemPtr nptr = (TypeMemPtr)nt;
      if( old == Type.NIL || old == Type.XNIL ) return nptr.ax_meet_nil(old);
      if( old == Type.SCALAR )
        return union(nt,old); // Result is a scalar, which changes the structure of the new types.
      if( old == Type.XSCALAR || old == Type.ANY ) break; // Result is the nt unchanged
      if( !(old instanceof TypeMemPtr) ) throw AA.unimpl(); // Not a xscalar, not a memptr, probably falls to scalar
      TypeMemPtr optr = (TypeMemPtr)old;
      nptr._aliases = nptr._aliases.meet(optr._aliases);
      nptr._obj = (TypeObj)ax_meet(bs,nptr._obj,optr._obj);
      break;
    }
    case TSTRUCT:
      if( old == TypeObj. OBJ || old == TypeObj.ISUSED ) { nt = old; break; }
      if( old == TypeObj.XOBJ || old == TypeObj.UNUSED ) break; // No changes, take nt as it is
      if( !(old instanceof TypeStruct) ) throw AA.unimpl();
      TypeStruct ots = (TypeStruct)old, nts = (TypeStruct)nt;
      // Meet all the non-recursive parts
      nts._any &= ots._any ;  nts._use = nts._any;
      nts._open|= ots._open;
      for( TypeFld ofld : ots.flds() ) {
        TypeFld nfld = nts.fld_find(ofld._fld);
        if( nfld == null ) {
          if( nts._any ) nts.add_fld(ofld); // New is high, so gets all the old fields
        } else {
          nfld.cmeet(ofld);     // Meet of non-recursive field parts
        }
      }
      // Remove new fields that are not in old.
      if( !ots._any )
        nts._flds.entrySet().removeIf( e -> !ots._flds.containsKey(e.getValue()._fld) );
      // Now recursively do all common fields
      for( TypeFld ofld : ots.flds() ) {
        TypeFld nfld = nts.fld_find(ofld._fld);
        if( nfld != null && nfld != ofld )
          nfld.setX(ax_meet(bs,nfld._t,ofld._t));
      }
      break;
    default: throw AA.unimpl();
    }
    return nt;
  }

  // Walk an existing, not-interned, structure.  Stop at any interned leaves.
  // Check for duplicating an interned Type or a UF hit, and use that instead.
  // Computes the final hash code.
  private static final IHashMap DUPS = new IHashMap();
  private TypeStruct shrink() {
    Ary<Type> reaches = reachable();
    assert DUPS.isEmpty();
    // Set all hashes.  Hash recursion stops at TypeStructs, so do them first.
    for( int i=0; i<reaches._len; i++ )
      if( reaches.at(i) instanceof TypeStruct ) reaches.at(i).set_hash();
    // Now TMPs
    for( int i=0; i<reaches._len; i++ )
      if( reaches.at(i) instanceof TypeMemPtr ) reaches.at(i).set_hash();
    for( int i=0; i<reaches._len; i++ )
      if( reaches.at(i) instanceof TypeFunPtr ) reaches.at(i).set_hash();
    // And all the rest.
    for( int i=0; i<reaches._len; i++ )
      reaches.at(i).set_hash();

    // Need back-edges to do this iteratively in 1 pass.  This algo just sweeps
    // until no more progress, but with generic looping instead of recursion.
    boolean progress = true;
    while( progress ) {
      progress = false;
      DUPS.clear();
      for( int j=0; j<reaches._len; j++ ) {
        Type t = reaches.at(j);
        Type t0 = ufind(t);
        Type t1 = t0.intern_lookup();
        if( t1==null ) t1 = DUPS.get(t0);
        if( t1 != null ) t1 = ufind(t1);
        if( t1 == t0 ) continue; // This one is already interned
        if( t1 != null ) { union(t0,t1); progress = true; continue; }

        switch( t._type ) {
        case TMEMPTR:           // Update TypeMemPtr internal field
          TypeMemPtr tm = (TypeMemPtr)t0;
          TypeObj t4 = tm._obj;
          TypeObj t5 = ufind(t4);
          if( t4 != t5 ) {
            tm._obj = t5;
            progress |= post_mod(tm);
            if( !t5.interned() ) reaches.push(t5);
          }
          break;
        case TFUNPTR:           // Update TypeFunPtr internal field
          TypeFunPtr tfptr = (TypeFunPtr)t0;
          Type t6 = tfptr._disp;
          Type t7 = ufind(t6);
          if( t6 != t7 ) {
            tfptr._disp = t7;
            progress |= post_mod(tfptr);
            if( !t7.interned() ) reaches.push(t7);
          }
          break;
        case TSTRUCT:           // Update all TypeStruct fields
          TypeStruct ts = (TypeStruct)t0;
          for( TypeFld tfld : ts._flds.values() ) {
            TypeFld tfld2 = ufind(tfld);
            if( tfld != tfld2 ) {
              progress = true;
              ts.set_fld(tfld2);
            }
          }
          break;
        case TFLD:              // Update all TFlds
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
    return ufind(this);
  }

  // Set hash after field mod, and re-install in dups
  private static boolean post_mod(Type t) {
    t._hash = t.compute_hash();
    DUPS.put(t);
    return true;
  }


  @SuppressWarnings("unchecked")
  private static <T extends Type> T ufind(T t) {
    T t0 = (T)UF.get(t._uid), tu;
    if( t0 == null ) return t;  // One step, hit end of line
    // Find end of U-F line
    while( (tu = (T)UF.get(t0._uid)) != null ) t0=tu;
    // Set whole line to 1-step end of line
    while( (tu = (T)UF.get(t ._uid)) != null ) { assert t._uid != t0._uid; UF.put(t._uid,t0); t=tu; }
    return t0;
  }
  private static <T extends Type> T union( T lost, T kept) {
    if( lost == kept ) return kept;
    assert !lost.interned();
    assert UF.get(lost._uid)==null && UF.get(kept._uid)==null;
    assert lost._uid != kept._uid;
    UF.put(lost._uid,kept);
    return kept;
  }

  // Walk, looking for prior interned
  private static boolean check_interned(Ary<Type> reachs) {
    for( Type t : reachs )
      if( t.intern_lookup() != null )
        return true;
    return false;
  }

  // Reachable collection of Types that form cycles: TypeMemPtr, TypeFunPtr,
  // TypeFld, TypeStruct, and anything not interned reachable from them.
  public Ary<Type> reachable() {
    Ary<Type> work = new Ary<>(new Type[1],0);
    push(work, this);
    int idx=0;
    while( idx < work._len ) {
      Type t = work.at(idx++);
      switch( t._type ) {
      case TMEMPTR:  push(work, ((TypeMemPtr)t)._obj ); break;
      case TFUNPTR:  push(work, ((TypeFunPtr)t)._disp); break;
      case TFLD   :  push(work, ((TypeFld   )t)._t   ); break;
      case TSTRUCT:  for( TypeFld tf : ((TypeStruct)t)._flds.values() ) push(work, tf); break;
      default: break;
      }
    }
    return work;
  }
  private void push( Ary<Type> work, Type t ) {
    if( !t.interned() && work.find(t)==-1 )
      work.push(t);
  }

  // Walk, looking for not-minimal.  Happens during 'approx' which might
  // require running several rounds of 'replace' to fold everything up.
  static boolean check_uf(Ary<Type> reaches) {
    int err=0;
    HashMap<Type,Type> ss = new HashMap<>();
    for( Type t : reaches ) {
      Type tt;
      if( ss.get(t) != null || // Found unresolved dup; ts0.equals(ts1) but ts0!=ts1
          ((tt = t.intern_lookup()) != null && tt != t) ||
          ufind(t) != t )
        err++;
      ss.put(t,t);
    }
    return err == 0;
  }

  // Set the cyclic bit on structs in cycles.  Set the hashcode for everything
  // reachable.  Stops at interned edges.  Can be modified to return e.g.
  // everything not-interned, or just members of cycles.  Can be handed an
  // arbitrary graph, including a DAG of unrelated Strongly Connected
  // Components.

  // Almost classic cycle-finding algorithm but since Structs have labeled
  // out-edges (with field names), we can have multiple output edges from the
  // same node (struct) to the same TypeMemPtr.  The classic cycle-finders do
  // not work with multi-edges.
  private static final Ary<Type> CSTACK = new Ary<>(Type.class);
  private static final VBitSet CVISIT = new VBitSet();
  private void get_cyclic( ) {
    assert CSTACK.isEmpty() && CVISIT.cardinality()==0;
    get_cyclic(this);
    assert CSTACK.isEmpty();
    CVISIT.clear();
  }
  private static void get_cyclic(Type t ) {
    t.set_hash();               // Set hash while we're here
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
    case TMEMPTR: get_cyclic(((TypeMemPtr)t)._obj ); break;
    case TFUNPTR: get_cyclic(((TypeFunPtr)t)._disp); break;
    case TFLD   : get_cyclic(((TypeFld   )t)._t   ); break;
    case TSTRUCT: CVISIT.set(t._uid); for( TypeFld fld : ((TypeStruct)t)._flds.values() ) get_cyclic(fld); break;
    default: break;
    }
    CSTACK.pop();               // Pop, not part of anothers cycle
  }


  // Buid a (recursively) sharpened pointer from memory.  Alias sets can be
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
    RECURSIVE_MEET++;
    TypeStruct mt = (TypeStruct)sharp._obj;
    mt = mt.shrink();                   // No shrinking nor UF expected
    Ary<Type> reaches = mt.reachable(); // Recompute reaches after shrink
    assert check_uf(reaches);
    UF.clear();
    RECURSIVE_MEET--;
    mt = mt.install_cyclic(reaches); // But yes cycles
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
    Type t = any ? TypeObj.ISUSED : TypeObj.UNUSED;
    for( int alias : dull._aliases )
      if( alias != 0 )
        for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) ) {
          TypeObj x = mem.at(kid);
          t = any ? t.join(x) : t.meet(x);
        }
    TypeMemPtr dptr = dull.make_from((TypeObj)t);
    if( _is_sharp(t) ) {        // If sharp, install and return
      mem.sharput(dull,dptr);
      return;
    }
    // Install in dull result in dull cache BEFORE recursing.  We might see it
    // again if cyclic types.
    dull_cache.put(dull._aliases,dptr);
    // Visit all dull pointers and recursively collect
    for( TypeFld fld : ((TypeStruct)t).flds() ) {
      Type tt = fld._t;
      if( tt instanceof TypeFunPtr ) tt = ((TypeFunPtr)tt)._disp;
      if( tt instanceof TypeMemPtr )
        _dull(mem,(TypeMemPtr)tt,dull_cache);
    }
  }
  // No dull pointers?
  private static boolean _is_sharp(Type t) {
    if( !(t instanceof TypeStruct) ) return true;
    TypeStruct ts = (TypeStruct)t;
    for( TypeFld fld : ts._flds.values() ) {
      Type tt = fld._t;
      assert fld.interned()==tt.interned();
      if( !tt.interned() ||     // Not interned internal, then this is not finished
          (tt instanceof TypeMemPtr && // Or has internal dull pointers
           ((TypeMemPtr)tt)._obj == TypeObj.ISUSED) )
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
    TypeStruct dts2 = ((TypeStruct)dptr._obj)._clone().set_hash();
    TypeMemPtr dptr2 = dptr.copy();
    dptr2._obj = dts2;
    dull_cache.put(dull._aliases,dptr2);
    // walk all fields, copy unless TMP.
    for( Map.Entry<String,TypeFld> e : dts2._flds.entrySet() ) {
      TypeFld fld = e.getValue();
      if( fld._t instanceof TypeMemPtr ) // For TMP, recurse on dull pointers.
        fld.setX(_sharp(mem,((TypeMemPtr)fld._t),dull_cache));
      if( fld._t instanceof TypeFunPtr ) {
        TypeFunPtr tf = (TypeFunPtr) fld._t;
        if( tf._disp instanceof TypeMemPtr ) { // Need  a pointer to sharpen
          TypeMemPtr dptr3 = _sharp(mem, (TypeMemPtr) tf._disp, dull_cache);
          fld.setX(dptr3.interned()             // Sharp return?
                   ? tf.make_from(dptr3)        // Make sharp TFP field
                   : tf._sharpen_clone(dptr3)); // Make dull  TFP field
        }
      }
      if( fld._t.interned() )
        e.setValue(fld.hashcons_free());
    }
    if( !_is_sharp(dts2) ) return dptr2; // Return the work-in-progress
    // Then copied field types are all sharp and interned.
    // Intern the fields themselves.
    for( Map.Entry<String,TypeFld> e : dts2._flds.entrySet() )
      if( !e.getValue()._t.interned() )
        e.setValue(e.getValue().hashcons_free());
    dull_cache.remove(dull._aliases);// Move the entry from dull cache to sharp cache
    TypeStruct sts = dts2.hashcons_free();
    return mem.sharput(dull,dull.make_from(sts));
  }

  @Override public Type meet_loop(Type t2) {
    //if( this==t2 ) return this;
    //if( !(t2 instanceof TypeStruct) ) return meet(t2);
    //if( _flds.length != ((TypeStruct)t2)._flds.length ) return meet(t2);
    //return xmeet1((TypeStruct)t2,true);
    throw unimpl();
  }

  // ------ Utilities -------

  // Field by name.
  public TypeFld fld_find( String name ) {
    assert !Util.eq(name,TypeFld.fldTop) && !Util.eq(name,TypeFld.fldBot);
    return _flds.get(name);
  }
  // Field type.  NPE if field-not-found
  public Type at( String name ) { return fld_find(name)._t; }
  // Field by index.  Error if not unique.
  public TypeFld fld_idx( int idx ) {
    // TODO: reverse map.
    TypeFld fx=null;
    for( TypeFld fld : _flds.values() ) {
      assert fld._order!=TypeFld.oTop && fld._order!=TypeFld.oBot;
      if( fld._order==idx ) {
        assert fx==null;        // Gotta be unique
        fx = fld;
      }
    }
    assert fx!=null;
    return fx;
  }

  // All fields for iterating.
  public Collection<TypeFld> flds() { return _flds.values(); }
  // Alpha sorted
  public Collection<TypeFld> asorted_flds() {
    TreeMap<String, TypeFld> sorted = new TreeMap<>();
    sorted.putAll(_flds);
    return sorted.values();
  }
  // Field order sorted
  public Collection<TypeFld> osorted_flds() {
    TreeMap<String, TypeFld> sorted = new TreeMap<>((f0,f1)->fld_find(f0)._order-fld_find(f1)._order);
    sorted.putAll(_flds);
    return sorted.values();
  }
  public int len() { return _flds.size(); } // Count of fields


  // Extend the current struct with a new named field, making a new struct
  public TypeStruct add_tup( Type t, int order ) { return add_fld(TypeFld.TUPS[order],Access.Final,t,order); }
  public TypeStruct add_fld( String name, Access mutable, int order ) { return add_fld(name,mutable,Type.SCALAR,order); }
  public TypeStruct add_fld( String name, Access mutable, Type tfld, int order ) {
    assert name==null || Util.eq(name,TypeFld.fldBot) || fld_find(name)==null;
    assert !_any && _open;
    TypeStruct ts = copy();
    ts.add_fld(TypeFld.make(name,tfld,mutable,order));
    return ts.hashcons_free();
  }
  // Replace an existing field in the current struct.
  public TypeStruct replace_fld( TypeFld fld ) { return copy().set_fld(fld).hashcons_free(); }
  public TypeStruct del_fld( String name ) {
    TypeStruct ts = copy();
    ts._flds.remove(name);
    return ts.hashcons_free();
  }

  // Update (approximately) the current TypeObj.  Updates the named field.
  @Override public TypeStruct update(Access fin, String fld, Type val) { return update(fin,fld,val,false); }

  TypeStruct update(Access fin, String name, Type val, boolean precise) {
    TypeFld fld = fld_find(name);
    if( fld == null ) return this; // Unknown field, assume changes no fields
    // Pointers & Memory to a Store can fall during GCP, and go from r/w to r/o
    // and the StoreNode output must remain monotonic.  This means store
    // updates are allowed to proceed even if in-error.
    if( fin==Access.Final || fin==Access.ReadOnly ) precise=false;
    Type   pval = precise ? val : fld._t.meet(val);
    Access pfin = precise ? fin : fld._access.meet(fin);
    TypeStruct ts = copy();
    ts.set_fld(fld.make_from(pval,pfin));
    return ts.hashcons_free();
  }

  @Override public TypeObj flatten_fields() {
    TypeStruct ts = malloc(_name,_any,_open);
    for( TypeFld fld : flds() )
      ts.add_fld(fld.make_from(fld._t.above_center() && fld._t!=Type.XNIL ? Type.XSCALAR : Type.SCALAR,Access.bot()));
    return ts.hashcons_free();
  }

  // Used during liveness propagation from Loads.
  // Fields not-loaded are not-live.
  @Override TypeObj remove_other_flds(String name, Type live) {
    TypeFld nfld = fld_find(name);
    if( nfld == null ) return UNUSED; // No such field, so all fields will be XSCALAR so UNUSED instead
    TypeStruct ts = _clone();
    for( Map.Entry<String,TypeFld> e : ts._flds.entrySet() ) {
      TypeFld fld = e.getValue();
      e.setValue(fld.setX( Util.eq(fld._fld,name) ? live : XSCALAR, Access.bot()).hashcons_free());
    }
    return ts.hashcons_free();
  }

  // Widen (lose info), to make it suitable as the default function memory.
  // All fields are widened to ALL (assuming a future error Store); field flags
  // set to bottom; only the field names are kept.
  @Override public TypeStruct crush() {
    if( _any ) return this;     // No crush on high structs
    TypeStruct st = malloc(_name,_any,_open);
    // Widen all fields, as-if crushed by errors, even finals.
    for( TypeFld fld : flds() )
      // Keep only the display pointer, as it cannot be stomped even with error code
      st.add_fld( Util.eq("^",fld._fld) ? fld : fld.make_from(Type.ALL,Access.bot()));
    return st.hashcons_free();
  }
  
  // Keep field names and orders.  Widen all field contents, including finals.
  // Handles cycles
  @Override public TypeStruct widen() {
    assert WIDEN_HASH.isEmpty();
    TypeStruct w = _widen();
    WIDEN_HASH.clear();
    return w;
  }

  private static final NonBlockingHashMapLong<TypeStruct> WIDEN_HASH = new NonBlockingHashMapLong<>();
  @Override TypeStruct _widen() {
    TypeStruct ts = WIDEN_HASH.get(_uid);
    if( ts!=null ) { ts._cyclic=true; return ts; }
    RECURSIVE_MEET++;
    ts = malloc(_name,_any,_open);
    WIDEN_HASH.put(_uid,ts);
    for( TypeFld fld : _flds.values() ) ts.add_fld(fld.malloc_from());
    ts.set_hash();
    for( TypeFld fld : ts._flds.values() ) fld.setX(fld._t._widen());
    if( --RECURSIVE_MEET == 0 )
      ts = ts.install();
    return ts;
  }

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t.isa(this) ) return 0; // TODO: really: test same flds, each fld isBitShape
    return 99;
  }

  @Override public Type meet_nil(Type nil) { return this; }

  @Override boolean contains( Type t, VBitSet bs ) {
    if( bs==null ) bs=new VBitSet();
    if( bs.tset(_uid) ) return false;
    for( TypeFld fld : _flds.values() ) if( fld._t==t || fld._t.contains(t,bs) ) return true;
    return false;
  }

  @Override public void walk( Predicate<Type> p ) {
    if( p.test(this) )
      for( TypeFld fld : _flds.values() ) fld.walk(p);
  }

  // Make a Type, replacing all dull pointers from the matching types in mem.
  @Override public TypeStruct make_from(Type head, TypeMem mem, VBitSet visit) {
    if( visit.tset(_uid) ) return null;
    TypeStruct ts = malloc(_name,_any,_open);
    for( TypeFld fld : flds() )
      ts.add_fld(fld.make_from(head,mem,visit));
    return ts.hashcons_free();
  }

  // Used for assertions
  @Override boolean intern_check1() {
    for( TypeFld fld : flds() )
      if( fld.intern_lookup()==null )
        return false;
    return true;
  }
}
