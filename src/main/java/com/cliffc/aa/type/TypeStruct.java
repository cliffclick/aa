package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.*;
import java.util.function.*;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFlds.sbefore;
import static com.cliffc.aa.type.TypeFld.Access;

/** A memory-based collection of named fields.  This is a recursive type,
 *  produced by NewNode and structure or tuple constants.  Fields can be
 *  indexed by field name (which can be a digit string, e.g. tuples), but NOT
 *  by a general number - that's an Array.
 *  <br>
 *  Structs represent a collection of ALL (infinitely many) fields, of which
 *  nearly all use the default field type.  The exceptions are explicitly
 *  listed.  Structs have a clazz name (by default empty) which is a colon
 *  separated list; parent clazzes on the left and child clazzes to the right.
 *  <br>
 *  The recursive type poses some interesting challenges.  It is represented as
 *  literally a cycle of pointers which must include a TypeStruct (and not a
 *  TypeTuple which only roots Types), a TypeMemPtr (edge) or a TypeFunPtr
 *  (display and return pointers) and a TypeFld.  Type inference involves
 *  finding the Meet of two cyclic structures.  The cycles will not generally
 *  be of the same length.  However, each field Meets independently (and fields
 *  in one structure but not the other use the infinite field rules).  This means
 *  we are NOT trying to solve the general problem of graph-equivalence (a
 *  known NP hard problem).  Instead, we can solve each field independently and
 *  also intersect across common fields.
 *  <br>
 *  When solving across a single field, we will find some prefix and then
 *  possibly a cycle - conceptually the type unrolls forever.  When doing the
 *  Meet we conceptually unroll both types forever, compute the Meet element by
 *  element... but when both types have looped, we can stop and the discovered
 *  cycle is the Meet's cycle.
 *  <br>
 *  After computing a possibly-cyclic type (via Meet or from-whole-cloth) we
 *  run a DFA minimization algorithm, then a cycle-aware hash and intern the
 *  result - possibly returning a previous cycle.
 */
public class TypeStruct extends Type<TypeStruct> implements Cyclic, Iterable<TypeFld> {
  static final HashMap<TPair,TypeStruct> MEETS0 = new HashMap<>();

  // Roughly a tree-shaped clazz designation.  A colon-separated list of clazz
  // names, which may be empty.  Parent clazzes on the left, child on the
  // right.  Used by Field lookups for final constant fields kept in the clazz
  // and not here.  A leading '~' character means the clazz is high instead of
  // low, mostly matters during meets to preserve symmetry.
  public String _clz;

  // Default field value.  Exceptions are listed below, all other (infinitely
  // many) fields are the default.
  public Type _def;

  // Interned field array.  Alpha-sorted.
  private TypeFld[] _flds;

  TypeStruct init( String clz, Type def, TypeFld[] flds ) {
    super.init();
    _clz  = clz;
    _def  = def;
    _flds = flds;
    assert check() && check_name(_clz);
    return this;
  }

  private static boolean check_name(String n) { return n.isEmpty() || Util.eq(n,"~") || n.charAt(n.length()-1)==':'; }
  // No instance of the default
  private boolean check() {
    for( TypeFld fld : _flds ) if( fld._t == _def ) return false; // Not canonical
    return true;
  }
  // Shallow clone, not interned BUT _flds IS INTERNED and cannot be hacked.
  // Used by e.g. Type.set_name.  Generally not suitable for TypeStruct hacking.
  @Override TypeStruct copy() { return _copy().init(_clz,_def,_flds); }

  // Shallow clone, not interned AND _flds is shallow cloned, NOT interned.
  // Suitable for hacking fields.
  TypeStruct copy2() { return _copy().init(_clz,_def,TypeFlds.clone(_flds)); }

  // --------------------------------------------------------------------------
  // Hash code computation and (cycle) Equals

  // Fairly subtle, because the typical hash code is built up from the hashes of
  // its parts, but the parts are not available during construction of a cyclic type.
  // We can count on the field names and accesses but not the type.
  @Override long static_hash() {
    Util.add_hash(super.static_hash() ^ _clz.hashCode());
    Util.add_hash(_def._hash);
    for( TypeFld fld : _flds )
      // Can depend on the field name and access, but NOT the type - because recursion.
      // Fields must be ordered, so hash can depend on order, so alpha-sorted already.
      Util.add_hash(fld._fld.hashCode() ^ fld._access.hashCode());
    return Util.get_hash();
  }

  // Returns 1 for definitely equals, 0 for definitely unequals, and -1 if
  // needing the cyclic test.
  private int cmp( TypeStruct t ) {
    if( !super.equals(t) || len() != t.len() || !Util.eq(_clz,t._clz) || _def!=t._def ) return 0;
    if( _flds==t._flds ) return 1;
    // All fields must be equals
    for( int i=0; i<_flds.length; i++ ) {
      TypeFld fld0 =   _flds[i]; // Get in order
      TypeFld fld1 = t._flds[i];
      int cmp = fld0.cmp(fld1);
      if( cmp!= 1 ) return cmp; // Fields do not match, or needs a cyclic check
    }
    return 1;                   // Everything is equals, right now
  }

  // Static properties equals, no edges.  Already known to be the same class
  // and not-equals.  May-equal fields are treated as equals
  @Override boolean static_eq( TypeStruct t ) {
    if( !super.equals(t) || len() != t.len() || !Util.eq(_clz,t._clz) || _def!=t._def ) return false;
    if( _flds==t._flds ) return true;
    // Fields are all alpha-sorted already
    for( int i=0; i<_flds.length; i++ ) {
      TypeFld fld1 =   _flds[i]; // Get in order
      TypeFld fld2 = t._flds[i]; // Get in order
      if( fld1.cmp(fld2)==0 ) return false;
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
    if( cyclic()==null && t.cyclic()==null )
      return super.equals(t) && TypeFlds.eq(_flds,t._flds) && Util.eq(_clz,t._clz) && _def==t._def;

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
    for( int i=0; i<_flds.length; i++ ) {
      Type t0 =   _flds[i]._t; // Get in order
      Type t1 = t._flds[i]._t;
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
  public static TypeStruct malloc( String clz, Type def, TypeFld[] flds ) {
    return POOLS[TSTRUCT].<TypeStruct>malloc().init(clz,def,flds);
  }
  // Used to make a few (larger and recursive) testing constants.  Some
  // fields are interned and some are recursive and without a type.
  public static TypeStruct malloc_test( String name, TypeFld fld0, TypeFld fld1 ) {
    return malloc(name,ALL,TypeFlds.make(fld0,fld1));
  }
  public TypeStruct hashcons_free() {
    // All subparts already interned
    if( RECURSIVE_MEET ==0 ) {
      for( TypeFld fld : _flds ) assert fld.interned();
      assert TypeFlds.interned(_flds);
    }
    return super.hashcons_free();
  }

  public static TypeStruct make( String clz, Type def, TypeFld[] flds ) { return malloc(clz,def,flds).hashcons_free(); }
  // Make using the fields, with no struct name, low and closed; typical for a
  // well-known structure.
  public static TypeStruct make( String clz, Type def, TypeFld fld0 ) { return make(clz,def,TypeFlds.make(fld0)); }
  public static TypeStruct make( TypeFld[] flds ) { return make("",ALL,flds); }
  public static TypeStruct make( TypeFld fld0 ) { return make(TypeFlds.make(fld0)); }
  public static TypeStruct make( TypeFld fld0, TypeFld fld1 ) { return make(TypeFlds.make(fld0,fld1)); }

  public static TypeStruct make( String clz, Type def, TypeFld fld0, TypeFld fld1 ) { return make(clz,def,TypeFlds.make(fld0,fld1)); }
  // Used to make a few testing constants
  public static TypeStruct make_test( String fld_name, Type t, Access a ) { return make(TypeFld.make(fld_name,t,a)); }

  public static TypeStruct make_int(TypeInt ti) { return TypeStruct.make("int:",ALL,TypeFld.make("$",ti)); }
  public static TypeStruct make_flt(TypeFlt tf) { return TypeStruct.make("flt:",ALL,TypeFld.make("$",tf)); }

  // Add a field to an under construction TypeStruct
  public TypeStruct add_fld( TypeFld fld ) {
    assert find(fld._fld)==-1;  // No accidental replacing
    _flds = TypeFlds.add(_flds,fld);
    return this;
  }

  // Set/replace a field to an under construction TypeStruct
  public TypeStruct set_fld( TypeFld fld ) {
    assert un_interned() && !TypeFlds.interned(_flds);       // No mutation if interned
    _flds[find(fld._fld)]=fld;
    return this;
  }

  // Make a named variant of any type, by just adding a name.
  public final TypeStruct set_name(String clz) {
    if( Util.eq(_clz,clz) ) return this;
    assert check_name(clz);
    TypeStruct ts = copy();
    ts._clz = clz;
    return ts.hashcons_free();
  }

  // Remove default dups.  'flds' is not-interned.
  static TypeFld[] remove_dups(Type def, TypeFld[] flds) {
    int cnt=0, i=0;
    for( TypeFld fld : flds )  if( fld._t == def )  cnt++;
    if( cnt==0 ) return flds;
    assert !TypeFlds.interned(flds);
    TypeFld[] fs = TypeFlds.get(flds.length-cnt);
    for( TypeFld fld : flds )  if( fld._t != def )  fs[i++]=fld;
    TypeFlds.free(flds);
    return fs;
  }
  static TypeStruct make0(String name, Type def, TypeFld[] flds) { return make(name,def,TypeFlds.hash_cons(remove_dups(def,flds))); }
  public TypeStruct make_from(TypeFld[] flds) { return make0(_clz,_def,flds); }
  public void remove_dups() { _flds = remove_dups(_def,_flds); }
  public void remove_dups_hashcons() { _flds = TypeFlds.hash_cons(remove_dups(_def,_flds)); }

  // Possibly allocated.  No fields specified.  All fields are possible and
  // might be ALL (error).  The worst possible result.
  public static final TypeStruct ISUSED = make("",ALL,TypeFlds.EMPTY);
  // Unused by anybody, perhaps not even allocated.  No fields specified.
  // All fields are available as ANY.
  public static final TypeStruct UNUSED = ISUSED.dual();

  // Wrapped primitive prototypes
  public static final TypeStruct INT = make_int(TypeInt.INT64);
  public static final TypeStruct FLT = make_flt(TypeFlt.FLT64);
  public static final TypeStruct BOOL= make_int(TypeInt.BOOL );
  public static final TypeStruct ZERO= make_int(TypeInt.ZERO );

  // A bunch of types for tests
  public  static final TypeStruct POINT = make(TypeFld.make("x",TypeFlt.FLT64),TypeFld.make("y",TypeFlt.FLT64));
  public  static final TypeStruct NAMEPT= POINT.set_name("Point:");
  public  static final TypeStruct A     = make_test("a",TypeFlt.FLT64,Access.Final);
  public  static final TypeStruct C0    = make_test("c",TypeInt.FALSE,Access.Final); // @{c:0}
  public  static final TypeStruct D1    = make_test("d",TypeInt.TRUE ,Access.Final); // @{d:1}
  public  static final TypeStruct ARW   = make_test("a",TypeFlt.FLT64,Access.RW   );

  // Pile of sample structs for testing
  static final TypeStruct[] TYPES = new TypeStruct[]{ISUSED,POINT,NAMEPT,A,C0,D1,ARW,INT,FLT};

  // --------------------------------------------------------------------------
  // Meet and dual

  // Dual the flds, dual the tuple.  Return a not-interned thing.
  @Override protected TypeStruct xdual() {
    TypeFld[] tfs = TypeFlds.get(len());
    for( int i=0; i<tfs.length; i++ )
      tfs[i] = _flds[i]._dual;
    return malloc(clz_dual(_clz), _def._dual, TypeFlds.hash_cons(tfs));
  }

  // Recursive dual
  @Override void rdual() {
    for( int i=0; i<_flds.length; i++ )
      _dual._flds[i] = _flds[i]._dual;
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
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TRPC:
    case TMEMPTR:return cross_nil(t);
    case TARY:
    case TFLD:
    case TTUPLE :
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeStruct that = (TypeStruct)t, mt;
    // INVARIANT: Both this and that are prior existing & interned.
    assert RECURSIVE_MEET > 0 || (interned() && that.interned());
    // INVARIANT: Both MEETS are empty at the start.  Nothing involved in a
    // potential cycle is interned until the Meet completes.
    assert RECURSIVE_MEET > 0 || (MEETS0.isEmpty());

    // Common name prefix
    String clz = clz_meet(_clz,that._clz);
    // Default never includes self, so can recursively meet
    Type def = _def.meet(that._def);

    // If both are cyclic, we have to do the complicated cyclic-aware meet
    return cyclic()!=null && that.cyclic()!=null
      ? cyclic_meet(that, clz, def)
      // Recursive but not cyclic; since at least one of these types is
      // non-cyclic.  Normal recursion will bottom-out.
      :   flat_meet(that, clz, def);
  }

  // Meet all common fields, using defaults for the uncommon fields.
  // Remove dups, remove defaults, sort.
  private static final Ary<TypeFld> FLDS = new Ary<>(new TypeFld[1],0);
  private TypeStruct flat_meet( TypeStruct that, String clz, Type def ) {
    TypeFld[] flds0 = TypeFlds.get(this.len()+that.len());
    int i=0, j=0, len0=0;
    while( i<this.len() && j<that.len() ) {
      TypeFld fld0 = this._flds[i], fld1 = that._flds[j];
      String    s0 = fld0._fld    ,   s1 = fld1._fld;
      if( fld0==fld1 )          { i++; j++; if( fld0._t!=def ) flds0[len0++] = fld0; } // Fast-path shortcut
      else if( Util.eq(s0,s1) ) { i++; j++; len0=add_fld(flds0,len0,s0,def,fld0._t.meet(fld1._t),fld0._access.meet(fld1._access)); }
      else if( sbefore(s0,s1) ) { i++;      len0=add_fld(flds0,len0,s0,def,fld0,that._def); }
      else                      { j++;      len0=add_fld(flds0,len0,s1,def,fld1,this._def); }
    }
    for( ; i<this.len(); i++ )  len0=add_fld(flds0,len0,this._flds[i]._fld,def,this._flds[i],that._def);
    for( ; j<that.len(); j++ )  len0=add_fld(flds0,len0,that._flds[j]._fld,def,that._flds[j],this._def);
    // Sorted, dups and defaults removed.
    TypeFld[] flds = TypeFlds.get(len0);
    System.arraycopy(flds0,0,flds,0,len0);
    TypeFlds.free(flds0);
    return make(clz,def,TypeFlds.hash_cons(flds));
  }

  private static int add_fld(TypeFld[] flds0, int len0, String fld, Type def, TypeFld fld0, Type odef) {
    return add_fld(flds0,len0,fld,def,fld0._t.meet(odef),fld0._access);
  }
  private static int add_fld(TypeFld[] flds0, int len0, String fld, Type def, Type t, Access access) {
    if( t!=def )
      flds0[len0++] = TypeFld.make(fld,t,access);
    return len0;
  }
  private static void add_fldc(TypeFld fld) { add_fldc(fld._fld,fld._access); }
  private static void add_fldc(String fld, Access access) { FLDS.push(TypeFld.malloc(fld,null,access)); }

  // Meet over clazz names.
  // TODO: will also need a unique lexical numbering, not just a name, to
  // handle the case of the same name used in two different scopes.
  private static String clz_meet(String s0, String s1) {
    if( Util.eq(s0,s1) ) return s0; // Fast path
    assert check_name(s0) && check_name(s1);
    // Peel off sign character
    boolean a0 = s0.length()>0 && s0.charAt(0)=='~';
    boolean a1 = s1.length()>0 && s1.charAt(0)=='~';
    if( a0 ) s0 = s0.substring(1).intern();
    if( a1 ) s1 = s1.substring(1).intern();

    // Sort by name length
    if( s0.length() > s1.length() ) { String tmp=s0; s0=s1; s1=tmp;  boolean x=a0; a0=a1; a1=x; }
    int x = 0, i;  char c;    // Last colon separator index
    // Find split point
    for( i = 0; i < s0.length(); i++ ) {
      if( (c=s0.charAt(i)) != s1.charAt(i) )
        break;
      if( c==':' ) x=i;
    }
    String s2;
    if( i==s0.length() ) {      // Have a common prefix?
      s2 = a0 ? s1 : s0;        // Short guy is high, keep long; short guy is low keep short
      if( a0&a1 ) s2 = ("~"+s2).intern();  // If high, add back sign character
    } else {                    // Mismatched, always use low prefix
      s2 = s0.substring(0,x).intern();
    }
    assert check_name(s2);
    return s2;
  }
  private static String clz_dual(String s0) {
    return s0.length()>0 && s0.charAt(0)=='~'
      ? s0.substring(1).intern()
      : ("~"+s0).intern();
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
  private TypeStruct cyclic_meet( TypeStruct that, String clz, Type def ) {
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
    // Do a shallow MEET: meet of field names and all things that can
    // be computed without the cycle.  Some fld._t not filled in yet.
    FLDS.clear();
    int i=0, j=0;
    while( i<this.len() && j<that.len() ) {
      TypeFld fld0 = this._flds[i], fld1 = that._flds[j];
      String    s0 = fld0._fld    ,   s1 = fld1._fld;
      if( fld0==fld1 )          { i++; j++; FLDS.push(fld0); } // Fast-path shortcut
      else if( Util.eq(s0,s1) ) { i++; j++; add_fldc(s0,fld0._access.meet(fld1._access)); }
      else if( sbefore(s0,s1) ) { i++;      add_fldc(fld0); }
      else                      { j++;      add_fldc(fld1); }
    }
    for( ; i<this.len(); i++ )  add_fldc(this._flds[i]);
    for( ; j<that.len(); j++ )  add_fldc(that._flds[j]);
    TypeFld[] flds = TypeFlds.get(FLDS.len());
    System.arraycopy(FLDS._es,0,flds,0,FLDS.len()); // Bulk fill without filtering
    mt = malloc(clz,def,flds);
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
    TypeFld[] flds = TypeFlds.get(len());
    for( int i=0; i<flds.length; i++ ) {
      TypeFld fld = _flds[i];
      Type t = fld._t.simple_ptr();
      flds[i] = fld._t==t ? fld : fld.make_from(t);
    }
    return make0(_clz,_def,flds);
  }

  // ------ Utilities -------
  // Clazz name, without leading "~"
  public String clz() {
    if( _clz.isEmpty() ) return _clz;
    return _clz.charAt(0)=='~' ? _dual._clz : _clz;
  }
  // All fields for iterating.
  public int len() { return _flds.length; } // Count of fields
  // Find index by name
  public int find( String name ) {
    for( int i=0; i<_flds.length; i++ )
      if( Util.eq(name,_flds[i]._fld) )
        return i;
    return -1;
  }
  // Field by name.
  public boolean has( String name ) { return find(name)!=-1; }
  public TypeFld get( String name ) {
    int idx = find(name);
    return idx==-1 ? null : _flds[idx];
  }
  // Field type by name.  NPE if field-not-found
  public Type at( String name ) { return get(name)._t; }

  // Field by index, null after end
  public TypeFld get( int idx ) { return idx < _flds.length ? _flds[idx] : null; }
  // Field type by index, AIOOBE if field not found
  public Type at( int idx ) { return _flds[idx]._t; }

  // Non-allocating iterator; pulls iterators from a pool.  The hard part is
  // telling when an iterator ends early, to avoid leaking.  This is not
  // exactly asserted for, so some leaks may happen.
  @Override public Iter iterator() { return Iter.get(this); }
  private static class Iter implements Iterator<TypeFld> {
    private static final Ary<Iter> POOL = new Ary<>(Iter.class);
    private static int CNT=0; // Number of Iters made, helps to track leaks
    TypeFld[] _flds;
    boolean _has_hash;
    int _i;
    static Iter get(TypeStruct ts) {
      if( POOL.isEmpty() ) { assert CNT<100; CNT++; new Iter().end(); }
      return POOL.pop().init(ts);
    }
    boolean end() { _i=-99; _flds=null; POOL.push(this); return false; }
    private Iter init(TypeStruct ts) { assert _i==-99; _i=0; _flds=ts._flds; _has_hash = ts._hash!=0; return this; }
    @Override public boolean hasNext() {  assert _i>=0; return _i < _flds.length || end(); }
    @Override public TypeFld next() { return _flds[_i++]; }
    @Override public void remove() {
      // i was pre-advanced, so remove field i-1
      assert !_has_hash;          // Changing, so underlying struct is mid-construction
      //_flds.remove(--_i);
      throw unimpl();
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
    for( int i=0; i<len(); i++ )
      _flds[i] = (TypeFld)map.map(_flds[i]);
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
    if( Util.eq(_clz,"int:") && has("$") ) return at("$")._str(visit,dups,sb,debug,false);
    if( Util.eq(_clz,"flt:") && has("$") ) return at("$")._str(visit,dups,sb,debug,false);

    sb.p(_clz);
    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    // Special shortcut for the all-prims display type
    if(      is_math()    )  sb.p("MATH");
    else if( is_file_dsp() ) sb.p("FILE_MEM");
    else if( is_int_clz()  ) sb.p("INT");
    else if( is_flt_clz()  ) sb.p("FLT");
    else {
      // Set the indent flag once for the entire struct.  Indent if any field is complex.
      boolean ind = false;
      for( TypeFld fld : this )
        if( (debug || !Util.eq(fld._fld,"^")) && (fld._t!=null && fld._t._str_complex(visit,dups)) )
          ind=indent;           // Field is complex, indent if asked to do so
      if( ind ) sb.ii(1);
      if( _def!=ALL )
        _def._str(visit,dups,sb, debug,indent).p(is_tup ? ", " : "; "); // Between fields
      for( TypeFld fld : _flds ) {
        if( !debug && Util.eq(fld._fld,"^") ) continue; // Do not print the ever-present display
        if( ind ) sb.nl().i();
        fld._str(visit,dups, sb, debug, indent ); // Field name, access mod, type
        sb.p(is_tup ? ", " : "; "); // Between fields
      }
      if( _flds.length>0 || _def!=ALL )    sb.unchar().unchar();
      if( ind ) sb.nl().di(1).i();
    }
    sb.p(!is_tup ? "}" : ")");
    return sb;
  }

  @Override boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) { return true; }

  boolean is_math() { return has("pi"); }
  boolean is_file_dsp() { return has("int") && has("flt") && has("math"); }
  boolean is_int_clz() { return has("!_"); }
  boolean is_flt_clz() { return has("_/_") && at("_/_") instanceof TypeFunPtr; }

  // e.g. (), (^=any), (^=any,"abc"), (3.14), (3.14,"abc"), (,,)
  static TypeStruct valueOf(Parse P, String cid, boolean is_tup, boolean any ) {
    if( is_tup ) P.require('(');
    else { P.require('@');  P.require('{'); }
    TypeStruct ts = malloc("",any ? ANY : ALL,TypeFlds.EMPTY);
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

  // Extend the current struct with a new named field, making a new struct
  public TypeStruct add_fldx( TypeFld fld ) { return make_from(TypeFlds.add(_flds,fld)); }
  // Replace an existing field in the current struct.
  public TypeStruct replace_fld( TypeFld fld ) {
    int idx = find(fld._fld);
    if( get(idx)==fld ) return this;
    return make_from(TypeFlds.make_from(_flds,idx,fld));
  }
  public TypeStruct pop_fld(int idx) {
    assert idx==_flds.length-1;
    return make_from(TypeFlds.pop(_flds));
  }

  // Update (approximately) the current TypeStruct.  Updates the named field.
  public TypeStruct update(Access fin, String name, Type val) {
    TypeFld fld = get(name);
    if( fld == null ) return this; // Unknown field, assume changes no fields
    // Double-final-stores, result is an error
    if( fld._access==Access.Final || fld._access==Access.ReadOnly )
      val = ALL;
    if( fld._t==ALL ) return this; // No changes if field is already in-error
    return replace_fld(fld.make_from(val,fin));
  }

  // Update (approximately) the whole current TypeStruct.
  // 'precise' is replace, imprecise is MEET.
  // 'live' tells if each field is alive or dead
  public TypeStruct update(TypeStruct ts, boolean precise, TypeStruct live) {
    return (TypeStruct)(precise ? ts : meet(ts)).join(live);
  }

  public TypeStruct flatten_fields() {
    TypeFld[] flds = TypeFlds.get(len());
    for( int i=0; i<_flds.length; i++ )
      flds[i] = _flds[i].make_from(SCALAR.oob(_flds[i]._t == XSCALAR || _flds[i]._t==ANY ), Access.bot());
    return make_from(flds);
  }

  // Used during liveness propagation from Loads.
  // Fields not-loaded are not-live.
  TypeStruct remove_other_flds(String name, Type live) {
    TypeFld nfld = get(name);
    if( nfld == null ) return UNUSED; // No such field, so all fields will be XSCALAR so UNUSED instead
    //TypeStruct ts = malloc(_clz,_def);
    //for( int i=0; i<len(); i++ ) {
    //  String fname = get(i)._fld;
    //  //ts._flds.push(TypeFld.make(fname,Util.eq(fname,name) ? live : XSCALAR, Access.bot()));
    //  throw unimpl();
    //}
    //return ts.hashcons_free();
    throw unimpl();
  }

  // Keep field names and orders.  Widen all field contents, including finals.
  // Handles cycles.
  @Override TypeStruct _widen() {
    TypeStruct ts = WIDEN_HASH.get(_uid);
    if( ts!=null ) throw unimpl(); // { ts.set_cyclic(); return ts; }
    RECURSIVE_MEET++;
    ts = copy2();               // Struct cloned, _flds cloned, fields referenced
    WIDEN_HASH.put(_uid,ts);
    for( int i=0; i<_flds.length; i++ )  ts._flds[i] = _flds[i].malloc_from(); // Clone fields
    for( TypeFld fld : ts._flds ) fld.setX(fld._t._widen());
    if( --RECURSIVE_MEET == 0 )
      ts = Cyclic.install(ts);
    return ts;
  }

  @Override public boolean above_center() { return _def.above_center(); }
  @Override public boolean is_con() {
    //if( !_def.is_con() ) return false;
    for( TypeFld fld : _flds )
      if( !fld.is_con() )
        return false;
    return true;
  }
  @Override public Type meet_nil(Type nil) {
    if( nil==XNIL ) {
      // Meet all fields, including the default, into XNIL.
      if( _def==ALL || _def==SCALAR ) return SCALAR; // Shortcut, ALL capped at SCALAR
      nil = _def.meet(XNIL);
      for( TypeFld fld : _flds )
        nil = nil.meet(fld._t);
      return nil==ALL ? SCALAR : nil;
    } else {
      // Meet NIL into all fields.
      TypeFld[] flds = TypeFlds.get(len());
      for( int i=0; i<flds.length; i++ )
        flds[i] = _flds[i].meet_nil(NIL);
      return make0(_clz,_def.meet_nil(NIL),flds);
    }
  }

  // Return the type without a nil-choice.  Only applies to above_center types,
  // as these are the only types with a nil-choice.  Only called during meets
  // with above-center types.  If called with below-center, there is no
  // nil-choice (might be a must-nil but not a choice-nil), so can return this.
  @Override TypeStruct not_nil() {
    TypeFld[] flds = TypeFlds.get(len());
    for( int i=0; i<flds.length; i++ )
      flds[i] = _flds[i].not_nil();
    return make0(_clz,_def.not_nil(),flds);
  }
  @Override public boolean must_nil() {
    // All must be !must_nil to be !must_nil.
    // If any are must_nil, the whole is must_nil
    if( _def.must_nil() ) return true;
    for( int i=0; i<len(); i++ )
      if( at(i).must_nil() )
        return true;
    return false;
  }
  @Override public boolean all_not_nil() {
    if( !_def.all_not_nil() ) return false;
    for( int i=0; i<len(); i++ )
      if( at(i).all_not_nil() )
        return false;
    return true;
  }
  @Override public boolean may_nil() {
    if( !_def.may_nil() ) return false;
    for( int i=0; i<len(); i++ )
      if( !at(i).may_nil() )
        return false;
    return true;
  }


  
  @Override boolean contains( Type t, VBitSet bs ) {
    if( bs==null ) bs=new VBitSet();
    if( bs.tset(_uid) ) return false;
    for( TypeFld fld : this ) if( fld._t==t || fld._t.contains(t,bs) ) return true;
    return false;
  }

  // Make a Type, replacing all dull pointers from the matching types in mem.
  @Override public TypeStruct make_from(Type head, TypeMem mem, VBitSet visit) {
    if( visit.tset(_uid) ) return null;
    //TypeStruct ts = malloc(_clz,_def);
    //for( TypeFld fld : this )
    //  ts.add_fld(fld.make_from(head,mem,visit));
    //return ts.hashcons_free();
    throw unimpl();
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
