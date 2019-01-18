package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Consumer;
import java.util.function.Predicate;

/** A memory-based Tuple with optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.  
 *
 *  The recursive type poses some interesting challenges.  It is represented as
 *  literally a cycle of pointers which must include a TypeStruct (and not a
 *  TypeTuple which only roots Types).  Type inference involves finding the
 *  Meet of two cyclic structures.  The cycles will not generally be of the
 *  same length.  However, each field Meets independently (and fields in one
 *  structure but not the other are not in the final Meet).  This means we are
 *  NOT trying to solve the general problem of graph-equivalence (a known hard
 *  problem).  Instead we can solve each field independently and also intersect
 *  across common fields.
 * 
 *  When solving across a single field, we will find some prefix and then
 *  possibly a cycle - conceptually the type unrolls forever.  When doing the
 *  Meet we conceptually unroll both types forever, compute the Meet element by
 *  element... but when both types have looped, we can stop and the discovered
 *  cycle is the Meet's cycle.
 */
public class TypeStruct extends TypeOop<TypeStruct> {
  // Fields are named in-order and aligned with the Tuple values.  Field names
  // are never null, and never zero-length.  If the 1st char is a '^' the field
  // is Top; a '.' is Bot; all other values are valid field names.
  public String[] _flds;        // The field names
  public Type[] _ts;            // Matching field types
  private int _hash; // Hash pre-computed to avoid large computes duing interning
  private TypeStruct     ( boolean any, String[] flds, Type[] ts ) { super(TSTRUCT, any); init(any,flds,ts); }
  private TypeStruct init( boolean any, String[] flds, Type[] ts ) {
    super.init(TSTRUCT, any);
    _flds=flds;
    _ts=ts;
    _uf=null;
    _hash= hash();
    return this;
  }
  private int hash() {
    int sum=0;
    for( String fld : _flds ) sum += fld==null ? 0 : fld.hashCode();
    return sum;
  }
  private static final Ary<TypeStruct> CYCLES = new Ary<>(new TypeStruct[0]);
  private TypeStruct find_other() {
    int idx = CYCLES.find(this);
    return idx != -1 ? CYCLES.at(idx^1) : null;
  }
  
  @Override public int hashCode( ) { return _hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return false;
    if( _ts == t._ts && _flds == t._flds ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( !_flds[i].equals(t._flds[i]) )
        return false;

    // Unlike all other non-cyclic structures which are built bottom-up, cyclic
    // types have to be built all-at-once, and thus hash-cons and equality-
    // tested with a cyclic-aware equals check.
    return cycle_equals(t);
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    TypeStruct t2 = find_other();
    if( t2 !=null ) return t2==t   ; // Already in cycle report equals or not
    TypeStruct t3 = t.find_other();
    if( t3 !=null ) return t3==this;// Already in cycle report equals or not
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return false;
    if( _ts == t._ts && _flds == t._flds ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( !_flds[i].equals(t._flds[i]) )
        return false;
    
    int len = CYCLES._len;
    CYCLES.add(this).add(t);
    boolean eq=cycle_equals0(t);
    CYCLES.remove(len);
    CYCLES.remove(len);
    return eq;
  }
  private boolean cycle_equals0( TypeStruct t ) {
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] &&   // Normally suffices to test ptr-equals only
          (_ts[i]==null || t._ts[i]==null || // Happens when asserting on partially-built cyclic types
           !_ts[i].cycle_equals(t._ts[i])) ) // Must do a full cycle-check
        return false;
    return true;
  }

  // Test if this is a cyclic value (and should not be interned) with internal
  // repeats.  i.e., not a minimal cycle.
  private TypeStruct repeats_in_cycles() {
    assert _cyclic;
    return repeats_in_cycles(this,new BitSet());
  }
  @Override TypeStruct repeats_in_cycles(TypeStruct head, BitSet bs) {
    if( bs.get(_uid) ) return null;
    bs.set(_uid);
    if( this!=head && equals(head) ) return this;
    for( Type t : _ts ) {
      TypeStruct ts = t.repeats_in_cycles(head,bs);
      if( ts!=null ) return ts;
    }
    return null;
  }
  
  String str( BitSet dups) {
    if( dups == null ) dups = new BitSet();
    else if( dups.get(_uid) ) return "*"; // Break recursive cycle
    dups.set(_uid);

    SB sb = new SB();
    if( _uf!=null ) return "=>"+_uf;
    if( _any ) sb.p('~');
    boolean is_tup = _flds.length==0 || fldTop(_flds[0]) || fldBot(_flds[0]);
    if( !is_tup ) sb.p('@');
    sb.p(is_tup ? '(' : '{');
    for( int i=0; i<_flds.length; i++ ) {
      if( !is_tup ) sb.p(_flds[i]);
      Type t = at(i);
      if( !is_tup && t != SCALAR ) sb.p(':');
      if( t != SCALAR ) sb.p(t==null ? "!" : t.str(dups));
      if( i<_flds.length-1 ) sb.p(',');
    }
    sb.p(!is_tup ? '}' : ')');
    return sb.toString();
  }

  // Unlike other types, TypeStruct never makes dups - instead it might make
  // cyclic types for which a DAG-like bottom-up-remove-dups approach cannot work.
  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  static TypeStruct malloc( boolean any, String[] flds, Type[] ts ) {
    if( FREE == null ) return new TypeStruct(any,flds,ts);
    TypeStruct t1 = FREE;  FREE = null;
    return t1.init(any,flds,ts);
  }
  private TypeStruct hashcons_free() { TypeStruct t2 = (TypeStruct)hashcons();  return this==t2 ? this : free(t2);  }

  // Default tuple field names - all bottom-field names
  private static final String[] FLD0={};
  private static final String[] FLD1={"."};
  private static final String[] FLD2={".","."};
  private static final String[] FLD3={".",".","."};
  private static final String[][] FLDS={FLD0,FLD1,FLD2,FLD3};
  public  static       String[] FLDS( int len ) { return FLDS[len]; }
  private static String[] flds(String... fs) { return fs; }
  private static Type[] ts(Type... ts) { return ts; }
  public  static TypeStruct make(Type... ts               ) { return malloc(false,FLDS[ts.length],ts).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type... ts) { return malloc(false,flds,ts).hashcons_free(); }

  private static final TypeStruct POINT = make(flds("x","y"),ts(TypeFlt.FLT64,TypeFlt.FLT64));
          static final TypeStruct X     = make(flds("x"),ts(TypeFlt.FLT64 )); // @{x:flt}
          static final TypeStruct TFLT64= make(          ts(TypeFlt.FLT64 )); //  (  flt)
  public  static final TypeStruct A     = make(flds("a"),ts(TypeFlt.FLT64 ));
  private static final TypeStruct C0    = make(flds("c"),ts(TypeNil.SCALAR)); // @{c:0}
  private static final TypeStruct D1    = make(flds("d"),ts(TypeInt.TRUE  )); // @{d:1}
  public  static final TypeStruct GENERIC = malloc(true,FLD0,new Type[0]).hashcons_free();

  // Recursive meet in progress
  private static final HashMap<TypeStruct,TypeStruct> MEETS1 = new HashMap<>(), MEETS2 = new HashMap<>();
  
  // Build a recursive struct type for tests: @{n=*?,v=flt}
  public static void init1() {
    Type dummy0 = TypeStr.STR; // Force TypeStr <clinit>
    Type dummy1 = TypeNil.NIL; // Force TypeNil <clinit>
    TypeStruct ts1 = malloc(false,new String[]{"n","v"},new Type[2]);
    RECURSIVE_MEET++;
    Type tsn = TypeNil.make(ts1);  tsn._cyclic = true;
    ts1._ts[0] = tsn;    ts1._cyclic = true;
    ts1._ts[1] = TypeFlt.FLT64;
    RECURSIVE_MEET--;
    RECURS_NIL_FLT = ts1.install_cyclic();

    ts1 = malloc(false,FLD2,new Type[2]);
    RECURSIVE_MEET++;
    tsn = TypeNil.make(ts1);  tsn._cyclic = true;
    ts1._ts[0] = tsn;    ts1._cyclic = true;
    ts1._ts[1] = TypeFlt.FLT64;
    RECURSIVE_MEET--;
    RECURT_NIL_FLT = ts1.install_cyclic();
    
  }
  public static TypeStruct RECURS_NIL_FLT, RECURT_NIL_FLT;
  
  static final TypeStruct[] TYPES = new TypeStruct[]{POINT,X,A,C0,D1};


  // Dual the flds, dual the tuple.
  @Override TypeStruct xdual() {
    String[] as = new String[_flds.length];
    Type  [] ts = new Type  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_flds[i]);
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeStruct(!_any,as,ts);
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    if( _dual != null ) return _dual;
    String[] as = new String[_flds.length];
    Type  [] ts = new Type  [_ts  .length];
    TypeStruct dual = _dual = new TypeStruct(!_any,as,ts);
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_flds[i]);
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].rdual();
    dual._hash = dual.hash();
    dual._dual = this;
    dual._cyclic = true;
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
    case TTUPLE :
    case TSTR:   return OOP;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TFUN:
    case TRPC:   return t.must_nil() ? SCALAR : NSCALR;
      
    case TNIL:
      // Cannot swap args and go again, because it screws up the cyclic_meet.
      // This means we handle struct-meet-nil right here.
      if( t == TypeNil.NIL ) return meet_nil();
      Type smt = meet(((TypeNil)t)._t);
      return t.above_center() ? smt : TypeNil.make(smt);
      
    case TOOP:
    case TNAME:  return t.xmeet(this); // Let other side decide
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeStruct thsi = this;
    TypeStruct that = (TypeStruct)t;
    // INVARIANT: Both this and that are prior existing & interned.
    assert RECURSIVE_MEET > 0 || (thsi.interned() && that.interned());
    // INVARIANT: Both MEETS are empty at the start.  Nothing involved in a
    // potential cycle is interned until the Meet completes.
    assert RECURSIVE_MEET > 0 || (MEETS1.isEmpty() && MEETS2.isEmpty());

    // If both are cyclic, we have to do the complicated cyclic-aware meet
    if( _cyclic && that._cyclic )
      return cyclic_meet(that);
    // Recursive but not cyclic; since at least one of these types is
    // non-cyclic normal recursion will bottom-out.

    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    return thsi._ts.length <= that._ts.length ? thsi.xmeet1(that) : that.xmeet1(thsi);
  }

  // Meet 2 structs, shorter is 'this'.
  private TypeStruct xmeet1( TypeStruct tmax ) {
    int len = _any ? tmax._ts.length : _ts.length;
    // Meet of common elements
    String[] as = new String[len];
    Type  [] ts = new Type  [len];
    for( int i=0; i<_ts.length; i++ ) {
      as[i] = smeet(_flds[i],tmax._flds[i]);
      ts[i] =    _ts[i].meet(tmax._ts  [i]); // Recursive not cyclic
    }
    // Elements only in the longer tuple
    for( int i=_ts.length; i<len; i++ ) {
      as[i] = tmax._flds[i];
      ts[i] = tmax._ts  [i];
    }
    return malloc(_any&tmax._any,as,ts).hashcons_free();
  }

  // Both structures are cyclic.  The meet will be "as if" both structures are
  // infinitely unrolled, Meeted, and then re-rolled.  If cycles are of uneven
  // length, the end result will be the cyclic GCD length.
  private TypeStruct cyclic_meet( TypeStruct that ) {
    // Walk 'this' and 'that' and map them both (via MEETS1 and MEETS2) to a
    // shared common Meet result.  Only walk the cyclic parts... cyclically.
    // When visiting a finite-sized part we use the normal recursive Meet.
    // When doing the cyclic part, we use the normal Meet except we need to use
    // the mapped Meet types.  As part of these Meet operations we can end up
    // Meeting Meet types with each other more than once, or more than once
    // from each side - which means already visited Types might need to Meet
    // again, even as they are embedded in other Types - which leads to the
    // need to use Tarjan U-F to union Types on the fly.

    // There are 4 choices here: this, that the existing MEETs from either
    // side.  U-F all choices together.  Some or all may be missing and can
    // be assumed equal to the final MEET.
    TypeStruct lf = MEETS1.get(this);
    TypeStruct rt = MEETS2.get(that);
    if( lf != null ) { lf = lf.ufind(); assert lf._cyclic && !lf.interned(); }
    if( rt != null ) { rt = rt.ufind(); assert rt._cyclic && !rt.interned(); }
    if( lf == rt && lf != null ) return lf; // Cycle has been closed

    // Take for the starting point MEET either already-mapped type.  If neither
    // is mapped, clone one (to make a new space to put new types into) and
    // simply point at the other - it will only be used for the len() and _any
    // fields.  If both are mapped, union together and pick one arbitrarily
    // (here always picked left).
    TypeStruct mt, mx;
    if( lf == null ) {
      if( rt == null ) { mt = this.shallow_clone(); mx = that; }
      else             { mt = rt;                   mx = this; }
    } else {
      if( rt == null ) { mt = lf;                   mx = that; }
      else             { mt = lf;  rt.union(lf);    mx = rt  ; }
    }
    MEETS1.put(this,mt);
    MEETS2.put(that,mt);

    // Do a shallow MEET: meet of field names and _any and _ts sizes - all
    // things that can be computed without the cycle.  _ts not filled in yet.
    int len = mt.len(mx); // Length depends on all the Structs Meet'ing here
    if( len != mt._ts.length ) {
      mt._flds= Arrays.copyOf(mt._flds, len);
      mt._ts  = Arrays.copyOf(mt._ts  , len);
    }
    if( mt._any && !mx._any ) mt._any=false;
    len = Math.min(len,mx._ts.length);
    for( int i=0; i<len; i++ )
      mt._flds[i] = smeet(mt._flds[i],mx._flds[i]); // Set the Meet of field names

    // Since the result is cyclic, we cannot test the cyclic parts for
    // pre-existence until the entire cycle is built.  We can't intern the
    // partially built parts, but we want to use the normal xmeet call - which
    // normally recursively interns.  Turn of interning with the global
    // RECURSIVE_MEET flag.
    RECURSIVE_MEET++;

    // For-all _ts edges do the Meet.  Some are not-recursive and mapped, some
    // are part of the cycle and mapped, some 
    for( int i=0; i<len; i++ ) {
      Type lfi = this._ts[i];
      Type rti = that._ts[i];
      Type mti = lfi.meet(rti); // Recursively meet, can update 'mt'
      Type mtx = mt._ts[i];     // Prior value, perhaps updated recursively
      Type mts = mtx.meet(mti); // Meet again
      assert mt._uf==null;      // writing results but value is ignored
      mt._ts[i] = mts;          // Finally update
    }

    // Lower recursive-meet flag.  At this point the Meet 'mt' is still
    // speculative and not interned.
    if( --RECURSIVE_MEET > 0 )
      return mt;                // And, if not yet done, just exit with it
    
    // This completes 'mt' as the Meet structure.
    return mt.install_cyclic();
  }

  // Install, cleanup and return
  TypeStruct install_cyclic() {
    // Check for dups.  If found, delete entire cycle, and return original.
    TypeStruct old = (TypeStruct)intern_lookup();
    // If the cycle already exists, just drop the new Type on the floor and let
    // GC get it and return the old Type.
    if( old == null ) {         // Not a dup
      assert repeats_in_cycles()==null;
      rdual();               // Complete cyclic dual
      // Insert all members of the cycle into the hashcons.  If self-symmetric,
      // also replace entire cycle with self at each point.
      if( equals(_dual) ) throw AA.unimpl();
      walk( t -> { if( t.interned() ) return false;
          t.retern()._dual.retern(); return true; });

      assert _ts[0].interned();
      old = this;
    }
    MEETS1.clear();
    MEETS2.clear();
    return old;
  }
  
  // Make a clone of this TypeStruct that is not interned.
  private TypeStruct shallow_clone() {
    assert _cyclic;
    Type[] ts = new Type[_ts.length];
    Arrays.fill(ts,Type.XSCALAR);
    TypeStruct tstr = malloc(_any,_flds.clone(),ts);
    tstr._cyclic = true;
    return tstr;
  }

  // Tarjan Union-Find to help build cyclic structures
  private TypeStruct _uf = null;
  private void union(TypeStruct tt) {
    assert !interned() && !tt.interned();
    assert _uf==null && tt._uf==null;
    if( this!=tt )
      _uf = tt;
  }
  private TypeStruct ufind() {
    if( _uf==null ) return this;
    if( _uf._uf==null ) return _uf;
    // Tarjan Union-Find
    throw AA.unimpl();
  }

  // THIS contains THAT, and THAT is too deep.  Make a new cyclic type for THIS
  // where THAT is replaced by THIS, before doing the Meet.
  private static final HashMap<Type,Type> MEET = new HashMap<>();
  public TypeStruct approx( final TypeStruct that ) {
    assert this.contains(that);
    // Recursively clone THIS, replacing the reference to THAT with the THIS clone.
    // Do not install until the cycle is complete.
    assert RECURSIVE_MEET == 0 && MEET.isEmpty();
    RECURSIVE_MEET++;
    TypeStruct mt = (TypeStruct)replace(that,null,MEET);
    // The result might not be minimal.  Look for a smaller cycle.
    TypeStruct mt2 = mt.repeats_in_cycles(); // Returns first dup instance
    if( mt2 != null ) // Shrink again
      mt = (TypeStruct)mt.replace(mt2,null,MEET);
    assert mt.repeats_in_cycles()==null; // TODO: Need to do this once-per-field?
    --RECURSIVE_MEET;
    assert RECURSIVE_MEET==0;
    MEET.clear();
    // Install the cycle
    return mt.install_cyclic();
  }

  // If unequal length; then if short is low it "wins" (result is short) else
  // short is high and it "loses" (result is long).
  private int len( TypeStruct tt ) { return _ts.length <= tt._ts.length ? len0(tt) : tt.len0(this); }
  private int len0( TypeStruct tmax ) { return _any ? tmax._ts.length : _ts.length; }
  
  static private boolean fldTop( String s ) { return s.charAt(0)=='^'; }
  static private boolean fldBot( String s ) { return s.charAt(0)=='.'; }
  // String meet
  private static String smeet( String s0, String s1 ) {
    if( s0 == null ) return s1;
    if( s1 == null ) return s0;
    if( fldTop(s0) ) return s1;
    if( fldTop(s1) ) return s0;
    if( fldBot(s0) ) return s0;
    if( fldBot(s1) ) return s1;
    if( s0.equals(s1) ) return s0;
    return "."; // fldBot
  }
  private static String sdual( String s ) {
    if( fldTop(s) ) return ".";
    if( fldBot(s) ) return "^";
    return s;
  }

  // Return the index of the matching field, or -1 if not found
  public int find( String fld ) {
    for( int i=0; i<_flds.length; i++ )
      if( fld.equals(_flds[i]) )
        return i;
    return -1;
  }

  public Type at( int idx ) { return _ts[idx]; }

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t.isa(this) ) return 0; // TODO: really: test same flds, each fld isBitShape
    if( t instanceof TypeName ) return 99; // Cannot pick up a name, requires user converts
    return 99;
  }
  // Build a depth-limited named type
  @Override TypeStruct make_recur(TypeName tn, int d, BitSet bs ) {
    // Mid-construction recursive types are always self-type
    for( Type t : _ts )  if( t == null )  return this;
    boolean eq = true;
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ )
      eq &= (ts[i] = _ts[i].make_recur(tn,d,bs))==_ts[i];
    return eq ? this : make(_flds,ts);
  }

  // Mark if part of a cycle
  @Override void mark_cycle( Type head, BitSet visit, BitSet cycle ) {
    if( visit.get(_uid) ) return;
    visit.set(_uid);
    if( this==head ) { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
    for( Type t : _ts ) {
      t.mark_cycle(head,visit,cycle);
      if( cycle.get(t._uid) )
        { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
    }
  }
  
  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { for( Type t : _ts) c.accept(t); }
  @Override public Type meet_nil() { return TypeNil.make(above_center() ? make(_flds,_ts) : this); }
  
  @Override boolean contains( Type t, BitSet bs ) {
    if( bs==null ) bs=new BitSet();
    if( bs.get(_uid) ) return false;
    bs.set(_uid);
    for( Type t2 : _ts) if( t2==t || t2.contains(t,bs) ) return true;
    return false;
  }
  @Override int depth( BitSet bs ) {
    if( _cyclic ) return 9999;
    if( bs==null ) bs=new BitSet();
    if( bs.get(_uid) ) return 0;
    bs.set(_uid);
    int max=0;
    for( Type t : _ts) max = Math.max(max,t.depth(bs));
    return max+1;
  }
  // Replace old with nnn in a 'this' clone.  We are initially called with
  // 'this==old', so in the clone there is a pointer to the initial
  // Type... which means the whole structure is cyclic when we are done.
  @Override Type replace( Type old, Type nnn, HashMap<Type,Type> HASHCONS ) {
    if( this==old ) return nnn; // Found a copy of 'old', so replace with 'nnn'
    if( _cyclic && !contains(old) ) // Not related, no need to update/clone
      return this;              // Just use as-is
    // Need to clone 'this'
    Type[] ts = new Type[_ts.length];
    TypeStruct rez = malloc(_any,_flds,ts);
    rez._cyclic=true;           // Whole structure is cyclic
    if( nnn==null ) nnn = rez;
    for( int i=0; i<_ts.length; i++ )
      ts[i] = _ts[i].replace(old,nnn,HASHCONS);
    return rez.hashcons_free();
  }
  @Override void walk( Predicate<Type> p ) {
    if( p.test(this) )
      for( Type _t : _ts ) _t.walk(p);
  }
}
