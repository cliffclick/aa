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
 *  nearly all use ANY/ALL.  The exceptions are explicitly listed.  Structs
 *  have a clazz name (by default empty) which is a colon separated list;
 *  parent clazzes on the left and child clazzes to the right.
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
public class TypeStruct extends TypeNil<TypeStruct> implements Cyclic, Iterable<TypeFld> {
  static final HashMap<TPair,TypeStruct> MEETS0 = new HashMap<>();

  // Roughly a tree-shaped clazz designation.  A colon-separated list of clazz
  // names, which may be empty.  Parent clazzes on the left, child on the
  // right.  Used by Field lookups for final constant fields kept in the clazz
  // and not here.
  public String _clz;

  // Default value
  public Type _def;

  // Interned field array.  Alpha-sorted to canonicalize.  Otherwise, unordered
  // to support e.g. row polymorphism.
  private TypeFld[] _flds;

  TypeStruct init( boolean any, boolean nil, boolean sub, String clz, Type def, TypeFld[] flds ) {
    super.init(any,nil,sub,BitsAlias.EMPTY,BitsFun.EMPTY);
    return _init(clz,def,flds);
  }
  TypeStruct init( boolean any, String clz, Type def, TypeFld[] flds ) {
    super.init(any,any,any,BitsAlias.EMPTY,BitsFun.EMPTY);
    return _init(clz,def,flds);
  }
  // Here already set any,nil,sub.  Now have def,fields.  Can finish checks.
  private TypeStruct _init( String clz, Type def, TypeFld[] flds ) {
    _def  = def;
    _clz  = clz;
    _flds = flds;
    assert check(def,flds) && check_name(clz);
    return this;
  }

  private static boolean check_name(String n) { return n.isEmpty() || n.charAt(n.length()-1)==':'; }
  // No instance of the default
  private static boolean check(Type def, TypeFld[] flds) {
    assert !(def instanceof TypeFld);
    for( TypeFld fld : flds ) if( fld!=null && fld._t == def ) return false; // Not canonical
    return true;
  }

  // Shallow clone, not interned BUT _flds IS INTERNED and cannot be hacked.
  // Used by e.g. Type.set_name.  Generally not suitable for TypeStruct hacking.
  @Override TypeStruct copy() {
    TypeStruct ts = super.copy();
    ts._clz = _clz;
    ts._def = _def;
    ts._flds = _flds;
    return ts;
  }

  // Shallow clone, not interned AND _flds is shallow cloned, NOT interned.
  // Suitable for hacking fields.
  TypeStruct copy2() {
    return copy().init(_any,_nil,_sub,_clz,_def,TypeFlds.clone(_flds));
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

  // --------------------------------------------------------------------------
  // Hash code computation and (cycle) Equals

  // Fairly subtle, because the typical hash code is built up from the hashes of
  // its parts, but the parts are not available during construction of a cyclic type.
  // We can count on the field names and accesses but not the type.
  @Override long static_hash() {
    Util.add_hash(super.static_hash() ^ _clz.hashCode() ^ _def.hashCode());
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
      return super.equals(t) && _flds==t._flds && Util.eq(_clz,t._clz) && _def==t._def;

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
  public static TypeStruct malloc( boolean any, boolean nil, boolean sub, String clz, Type def, TypeFld[] flds ) {
    return POOLS[TSTRUCT].<TypeStruct>malloc().init(any,nil,sub,clz,def,flds);
  }
  public static TypeStruct malloc( boolean any, String clz, Type def, TypeFld[] flds ) {
    return POOLS[TSTRUCT].<TypeStruct>malloc().init(any,clz,def,flds);
  }
  // Used to make a few (larger and recursive) testing constants.  Some
  // fields are interned and some are recursive and without a type.
  public static TypeStruct malloc_test( String name, TypeFld fld0, TypeFld fld1 ) {
    return malloc(false,name,ALL,TypeFlds.make(fld0,fld1));
  }
  public TypeStruct hashcons_free() {
    // All subparts already interned
    if( RECURSIVE_MEET ==0 ) {
      for( TypeFld fld : _flds ) assert fld.interned();
      assert TypeFlds.interned(_flds);
    }
    return super.hashcons_free();
  }
  void flds_free() {
    assert !TypeFlds.interned(_flds);
    TypeFlds.free(_flds);
    _flds=null;
  }

  // Generally purpose all-fields make
  public static TypeStruct make( boolean any, String clz, Type def, TypeFld[] flds ) {
    return malloc(any,clz,def,flds).hashcons_free();
  }
  private static TypeStruct make( boolean any, boolean nil, boolean sub, String clz, Type def, TypeFld[] flds ) {
    return malloc(any,nil,sub,clz,def,flds).hashcons_free();
  }
  // Make using the fields, with no struct name, low and closed; typical for a
  // well-known structure.
  public static TypeStruct make( TypeFld[] flds ) { return make(false,"",ALL,flds); }
  public static TypeStruct make( TypeFld fld0 ) { return make(TypeFlds.make(fld0)); }

  // The TypeFld[] is not interned.
  public static TypeStruct make_flds(String clz, Type def, TypeFld[] flds) { return make(false,clz,def,TypeFlds.hash_cons(remove_dups(def,flds))); }
  public static TypeStruct make_flds(String clz, Type def, TypeFld fld0, TypeFld fld1) { return make_flds(clz,def,TypeFlds.ts(fld0,fld1)); }

  // Used to make a few testing constants
  public static TypeStruct make_test( TypeFld fld0, TypeFld fld1 ) { return make(TypeFlds.make(fld0,fld1)); }
  public static TypeStruct make_test( String clz, Type def, TypeFld fld0, TypeFld fld1 ) { return make(false,clz,def,TypeFlds.make(fld0,fld1)); }
  public static TypeStruct make_test( String fld_name, Type t, Access a ) { return make(TypeFld.make(fld_name,t,a)); }

  // Add a field to an under construction TypeStruct; _flds is not interned.
  public TypeStruct add_fld( TypeFld fld ) {
    assert find(fld._fld)==-1 && !TypeFlds.interned(_flds);  // No accidental replacing, not interned
    TypeFld[] old = _flds;      // Keep the old
    _flds = TypeFlds.add_sort(_flds,fld);
    TypeFlds.free(old);         // Free the old
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
    assert !TypeFlds.interned(flds);
    int cnt=0, i=0;
    for( TypeFld fld : flds )  if( fld._t == def )  cnt++;
    if( cnt==0 ) return flds;
    TypeFld[] fs = TypeFlds.get(flds.length-cnt);
    for( TypeFld fld : flds )  if( fld._t != def )  fs[i++]=fld;
    TypeFlds.free(flds);
    return fs;
  }
  public void remove_dups() { _flds = remove_dups(_def,_flds); }
  public void remove_dups_hashcons() { _flds = TypeFlds.hash_cons(remove_dups(_def,_flds)); }
  // Replace _flds; flds is not interned
  public TypeStruct make_from(TypeFld[] flds) { return make(_any,_clz,_def,TypeFlds.hash_cons(remove_dups(_def,flds))); }


  public boolean is_str() { return Util.eq(_clz,"str:"); }

  // Make, replacing nil/sub flags
  //@Override TypeStruct make_from( boolean any, boolean nil, boolean sub ) { return make( any,nil,sub,_clz,_def,_flds); }



  // Possibly allocated.  No fields specified.  All fields are possible and
  // might be ALL (error).  The worst possible result.
  public static final TypeStruct ISUSED = make(TypeFlds.EMPTY);
  // Unused by anybody, perhaps not even allocated.  No fields specified.
  // All fields are available as ANY.
  public static final TypeStruct UNUSED = ISUSED.dual();

  // A bunch of types for tests
  public  static final TypeStruct POINT = make_test(TypeFld.make("x",TypeFlt.FLT64),TypeFld.make("y",TypeFlt.FLT64));
  public  static final TypeStruct NAMEPT= POINT.set_name("Point:");
  public  static final TypeStruct A     = make_test("a",TypeFlt.FLT64,Access.Final);
  public  static final TypeStruct C0    = make_test("c",TypeNil.XNIL ,Access.Final); // @{c:0}
  public  static final TypeStruct D1    = make_test("d",TypeInt.TRUE ,Access.Final); // @{d:1}
  public  static final TypeStruct ARW   = make_test("a",TypeFlt.FLT64,Access.RW   );

  // Pile of sample structs for testing
  static final TypeStruct[] TYPES = new TypeStruct[]{ISUSED,POINT,NAMEPT,A,C0,D1,ARW};

  // --------------------------------------------------------------------------
  // Meet and dual

  // Dual the flds, dual the tuple.  Return a not-interned thing.
  @Override protected TypeStruct xdual() {
    boolean is_con= _def == _def._dual;
    TypeFld[] tfs = TypeFlds.get(len());
    for( int i=0; i<tfs.length; i++ ) {
      tfs[i] = _flds[i]._dual;
      is_con &= tfs[i] == _flds[i];
    }
    if( is_con ) return this;   // On centerline, a constant struct
    //String dclz = clz_dual(_clz);
    boolean xor = _nil == _sub;
    return malloc(!_any, _nil^xor, _sub^xor, _clz, _def._dual, TypeFlds.hash_cons(tfs));
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
  @Override protected TypeStruct xmeet( Type t ) {
    TypeStruct that = (TypeStruct)t;
    // INVARIANT: Both this and that are prior existing & interned.
    assert RECURSIVE_MEET > 0 || (interned() && that.interned());
    // INVARIANT: Both MEETS are empty at the start.  Nothing involved in a
    // potential cycle is interned until the Meet completes.
    assert RECURSIVE_MEET > 0 || (MEETS0.isEmpty());

    // Common name prefix
    String clz = clz_meet(_clz,that._clz,_any,that._any);
    Type def = _def.meet(that._def);
    boolean any = _any & that._any;

    // If both are cyclic, we have to do the complicated cyclic-aware meet
    return cyclic()!=null && that.cyclic()!=null
      ? cyclic_meet(that, clz, def, any )
      // Recursive but not cyclic; since at least one of these types is
      // non-cyclic.  Normal recursion will bottom-out.
      :   flat_meet(that, clz, def, any );
  }

  // Meet all common fields, using defaults for the uncommon fields.
  // Remove dups, remove defaults, sort.
  private static final Ary<TypeFld> FLDS = new Ary<>(new TypeFld[1],0);
  private TypeStruct flat_meet( TypeStruct that, String clz, Type def, boolean any ) {
    TypeFld[] flds2 = TypeFlds.get(this.len()+that.len());
    int i=0, j=0, k=0;
    while( i<this.len() && j<that.len() ) {
      TypeFld fld0 = this._flds[i], fld1 = that._flds[j];
      String    s0 = fld0._fld    ,   s1 = fld1._fld;
      if( fld0==fld1 )          { i++; j++; if( fld0._t!=def ) flds2[k++] = fld0; } // Fast-path shortcut
      else if( Util.eq(s0,s1) ) { i++; j++; k = add_fld(flds2,k,s0,def,fld0._t.meet(fld1._t),fld0._access.meet(fld1._access)); }
      else if( sbefore(s0,s1) ) { i++;      k = add_fld(flds2,k,s0,def,fld0,that._def); }
      else                      {      j++; k = add_fld(flds2,k,s1,def,fld1,this._def); }
    }
    for( ; i<this.len(); i++ )  k = add_fld(flds2,k,this._flds[i]._fld,def,this._flds[i],that._def);
    for( ; j<that.len(); j++ )  k = add_fld(flds2,k,that._flds[j]._fld,def,that._flds[j],this._def);

    // Sorted, dups and defaults removed.
    TypeFld[] flds = TypeFlds.get(k);
    System.arraycopy(flds2,0,flds,0,k);
    TypeFlds.free(flds2);
    return make( any,
                 _nil & that._nil,
                 _sub & that._sub,
                 clz, def, TypeFlds.hash_cons(flds));
  }

  private static int add_fld(TypeFld[] flds2, int k, String fld, Type def, TypeFld fld0, Type odef) {
    return add_fld(flds2,k,fld,def,fld0._t.meet(odef),fld0._access);
  }
  private static int add_fld(TypeFld[] flds2, int k, String fld, Type def, Type t, Access access) {
    if( t!=def )
      flds2[k++] = TypeFld.make(fld,t,access);
    return k;
  }

  private static void add_fldc(TypeFld fld) { add_fldc(fld._fld,fld._access); }
  private static void add_fldc(String fld, Access access) { FLDS.push(TypeFld.malloc(fld,null,access)); }

  // Meet over clazz names.
  // TODO: will also need a unique lexical numbering, not just a name, to
  // handle the case of the same name used in two different scopes.
  public static String clz_meet(String s0, String s1, boolean a0, boolean a1) {
    if( Util.eq(s0,s1) ) return s0; // Fast path
    assert check_name(s0) && check_name(s1);

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
    } else {                    // Mismatched, always use low prefix
      s2 = s0.substring(0,x).intern();
    }
    assert check_name(s2);
    return s2;
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
  private TypeStruct cyclic_meet( TypeStruct that, String clz, Type def, boolean any ) {
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
    mt = malloc( any,
                _nil & that._nil,
                _sub & that._sub,
                clz,def,flds);
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
      Type lfi = lff == null ? this._def : lff._t;
      Type rti = rtf == null ? that._def : rtf._t;
      Type mti = lfi.meet(rti);
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
    return make_from(flds);
  }

  // ------ Utilities -------
  // Clazz name
  public String clz() { return _clz; }
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
  // Field type by name, or the default.
  public Type at_def( String name ) {
    int idx = find(name);
    return idx==-1 ? _def : _flds[idx]._t;
  }

  // Field by index, null after end
  public TypeFld fld( int idx ) { return idx < _flds.length ? _flds[idx] : null; }
  public TypeFld get( int idx ) { return fld(idx); }
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

  static boolean isDigit(char c) { return '0' <= c && c <= '9'; }
  public boolean is_tup() {
    int len = len();
    if( len==0 || (len==1 && get("^")!=null) ) return true;
    for( int i=0; i<len; i++ )
      if( isDigit(_flds[i]._fld.charAt(0)) ) return true;
    return false;
  }

  @Override public void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"S"+(char)('A'+ucnt._ts++));
      return;
    }
    // Do not walk the primitive prototype from the primitive, because it will
    // use short-cut printing.
    if( (Util.eq("int:",_clz) || Util.eq("flt:",_clz)) && get(".")!=null )
      return;

    for( int i=0; i<len(); i++ ) // DO NOT USE iter syntax, else toString fails when the iter pool exhausts during a debug session
      if( get(i)!=null )
        get(i)._str_dups(visit,dups,ucnt);
  }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    _strn(sb);
    // To distinguish "DUP:(...)" from "CLZ:(...)" we require another ':' IFF DUP is present.
    //           ()  -- parses as a no-dup no-clz tuple
    //       clz:()  -- parses as a no-dup    clz tuple
    //   dup:   :()  -- parses as a    dup no-clz tuple
    //   dup:clz:()  -- parses as a    dup    clz tuple
    //       int:1234
    //       flt:3.14
    // Shortcut print for 'int:1234" and 'flt:3.14'
    TypeFld tf;
    if( is_top_clz() ) return sb.p("@{TOP}");
    if( is_int_clz() ) return sb.p("@{INT}");
    if( is_flt_clz() ) return sb.p("@{FLT}");
    if( is_str_clz() ) return sb.p("str");
    if( is_math_clz()) return sb.p("@{MATH}");

    sb.p(_clz); // Includes a trailing ':' if not-empty
    if( _clz.isEmpty() && dups.get(_uid)!=null )  sb.p(':');

    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    // Set the indent flag once for the entire struct.  Indent if any field is complex.
    boolean ind = false;
    for( TypeFld fld : this )
      if( (debug || !Util.eq(fld._fld,"^")) && (fld._t!=null && fld._t._str_complex(visit,dups)) )
        ind=indent;           // Field is complex, indent if asked to do so
    if( ind ) sb.ii(1);
    boolean sep=false;
    for( TypeFld fld : _flds ) {
      if( !debug && Util.eq(fld._fld,"^") ) continue;
      if( fld==TypeFld.ANY_DSP ) sb.p('_'); // Short-cut the ever-present display
      else {
        if( ind ) sb.nl().i();
        fld._str(visit,dups, sb, debug, indent ); // Field name, access mod, type
      }
      sb.p(is_tup ? ", " : "; "); // Between fields
      sep=true;
    }
    if( _def==ANY ) sb.p("..."); // Any extra fields are allowed
    else if( _def==ALL ) {       // No extra fields
      if( sep ) sb.unchar().unchar();
    } else sb.p('$').p(_def);    // Unusual extra fields
    if( ind ) sb.nl().di(1).i();
    sb.p(!is_tup ? "}" : ")");
    return sb;
  }

  @Override boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) { return true; }

  boolean is_top_clz () { return _clz.isEmpty() && _flds.length>1 && Util.eq("math",_flds[1]._fld); }
  boolean is_int_clz () { return _clz.isEmpty() && _flds.length>0 && Util.eq("!_" ,_flds[0]._fld); }
  boolean is_flt_clz () { return _clz.isEmpty() && _flds.length>0 && Util.eq("-_" ,_flds[0]._fld); }
  boolean is_str_clz () { return _clz.isEmpty() && _flds.length>0 && Util.eq("#_" ,_flds[0]._fld); }
  boolean is_math_clz() { return _clz.isEmpty() && _flds.length>0 && Util.eq("pi" ,_flds[0]._fld); }


  // e.g. (), (^=any), (^=any,"abc"), (3.14), (3.14,"abc",:=123)
  // @{}, @{x=3.14; y="abc"; z:=123}
  static TypeStruct valueOf(Parse P, String dup, boolean any, boolean is_tup ) {
    TypeStruct ts = malloc(any,"",ALL.oob(any),TypeFlds.get(0));
    if( dup!=null ) P._dups.put(dup,ts);
    String clz = P.id();
    if( clz!=null ) {
      P.require(':');
      ts._clz = (clz+":").intern();
    }
    if( !is_tup ) { P.require('@');  P.require('{'); } else P.require('(');
    char close = is_tup ? ')' : '}';
    if( P.peek(close) ) return ts;

    int fld_num = 0;
    while(true) {
      if( P.peek("...") ) { assert any; break; }
      if( P.peek('$') )
        { ts._def = (TypeNil)P.type(null,false,-2); break; }
      TypeFld fld = ts.len()==0 && P.peek('_')
        ? TypeFld.ANY_DSP
        // Request a parse of:
        //   label:=type (yielding a TypeFld); label can be a number; or
        //   type (yielding a "fld_num=" type TypeFld) or
        // Handling of leading DUP: handled by general parser:
        //   DUP:label:=type (yielding a TypeFld) or
        //   DUP:type (yielding a "fld_num=" type TypeFld) or
        : (TypeFld)P.type(null,false,is_tup ? fld_num : -1/*must find a label*/);
      if( is_tup && fld._fld.equals(""+fld_num) ) fld_num++; // Used up a field num
      ts.add_fld(fld);
      if( !P.peek(is_tup ? ',' : ';') ) break;
    }
    P.require(close);
    return ts;
  }

  // Extend the current struct with a new named field, making a new struct
  public TypeStruct add_fldx( TypeFld fld ) { return make_from(TypeFlds.add_sort(_flds,fld)); }
  // Replace an existing field in the current struct.
  public TypeStruct replace_fld( TypeFld fld ) {
    int idx = find(fld._fld);
    if( idx==-1 ) return add_fldx(fld);
    if( get(idx)==fld ) return this;
    return make_from(TypeFlds.make_from(_flds,idx,fld));
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
  public TypeStruct update(TypeStruct ts, boolean precise) {
    return (TypeStruct)(precise ? ts : meet(ts));
  }

  // Widen all mutable fields to final ALL, for building default Parm inputs.
  public TypeStruct widen_mut_fields() {
    TypeFld[] flds = TypeFlds.get(len());
    for( int i=0; i<_flds.length; i++ )
      flds[i] = _flds[i]._access==Access.Final
        ? _flds[i]
        : _flds[i].make_from(TypeNil.SCALAR, Access.bot());
    return make_from(flds);
  }

  // Flatten fields for LIVE: only need a per-field any/all indication
  public TypeStruct flatten_live_fields() {
    boolean change=false;
    for( TypeFld fld : _flds )
      if( fld._t != Type.ANY || fld._t != Type.ALL )
        { change = true; break; }
    if( !change ) return this;
    TypeFld[] flds = TypeFlds.get(len());
    for( int i=0; i<_flds.length; i++ )
      flds[i] = _flds[i].make_from(_flds[i]._t==Type.ANY ? Type.ANY : Type.ALL, Access.bot());
    return make_from(flds);
  }

  @Override public boolean is_con() {
    if( !_def.is_con() ) return false;
    for( TypeFld fld : _flds )
      if( !fld.is_con() )
        return false;
    return true;
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

  public static TypeStruct as_struct( Type t ) {
    return t instanceof TypeStruct ts ? ts : t.oob(ISUSED);
  }
  
  // Used for assertions
  @Override boolean intern_check1() {
    for( TypeFld fld : this )
      if( fld.intern_get()==null )
        return false;
    return true;
  }

  public static void init1() {
    TypeStruct.RECURSIVE_MEET=0;
  }
}
