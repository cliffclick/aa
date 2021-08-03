package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;

import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.type.TypeFld.Access;
import static com.cliffc.aa.type.TypeMemPtr.NO_DISP;

/** A memory-based collection of optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.  Fields
 *  can be indexed by field name or numeric constant (i.e. tuples), but NOT by
 *  a general number - thats an Array.  Field access mods make a small lattice
 *  of: {choice,r/w,final,r-o}.  Note that mixing r/w and final moves to r-o and
 *  loses the final property.
 *
 *  The recursive type poses some interesting challenges.  It is represented as
 *  literally a cycle of pointers which must include a TypeStruct (and not a
 *  TypeTuple which only roots Types) and a TypeMemPtr (edge) or a TypeFunPtr
 *  (display pointer).  Type inference involves finding the Meet of two cyclic
 *  structures.  The cycles will not generally be of the same length.  However,
 *  each field Meets independently (and fields in one structure but not the
 *  other are not in the final Meet).  This means we are NOT trying to solve
 *  the general problem of graph-equivalence (a known NP hard problem).
 *  Instead we can solve each field independently and also intersect across
 *  common fields.
 *
 *  When solving across a single field, we will find some prefix and then
 *  possibly a cycle - conceptually the type unrolls forever.  When doing the
 *  Meet we conceptually unroll both types forever, compute the Meet element by
 *  element... but when both types have looped, we can stop and the discovered
 *  cycle is the Meet's cycle.

TODO:
 Cleaning up this mess somewhat... move the field parts into a TypeFld struct.
 TypeFld has: name, scalar Type, mod bits, a field-order number (includes a
 conforming Top and a undefined Bot field order).
 TypeStruct uses a private TypeFld[] with a decent set of accessors: at/looping.
 The TypeFld[] comes from Types so fast == check.
 A try-with-resources:
    try( Ary<TypeFld> flds = TypeFld.get_flds()) {
      while( pred ) flds.push(fld); // Accumulate, drop dups, screw around
      malloc(... flds ...); // Finally use
    } // Exit unwinds the get_flds
These can be scope-alloced from a free-list.


 */
public class TypeStruct extends TypeObj<TypeStruct> {
  public TypeFld[] _flds; // The fields.  Effectively final.  Public for iteration.
  public boolean _open;   // Fields after _fld.length are treated as ALL (or ANY)

  public boolean _cyclic; // Type is cyclic.  This is a summary property, not a part of the type, hence is not in the equals nor hash
  private TypeStruct init( String name, boolean any, TypeFld[] flds, boolean open ) {
    super.init(TSTRUCT, name, any, any);
    _flds  = flds;
    _open  = open;
    return this;
  }

  // Hash code computation.
  // Fairly subtle, because the typical hash code is built up from the hashes of
  // its parts, but the parts are not available during construction of a cyclic type.
  // TODO: If not cyclic, do a proper recursive hash
  @Override public int compute_hash() {
    int hash1 = super.compute_hash(), hash = hash1 +(_open?1023:0);
    assert hash1 != 0;
    // Compute hash from field names and orders and access.
    for( TypeFld fld : _flds ) { assert fld._hash!=0; hash = (hash + fld._hash) | (hash >>> 17); }
    return hash == 0 ? hash1 : hash;
  }

  // Returns 1 for definitely equals, 0 for definitely unequals, and -1 if
  // needing the cyclic test.
  private int cmp( TypeStruct t ) {
    if( !super.equals(t) ) return 0;
    if( _flds.length != t._flds.length || _open != t._open ) return 0;
    if( _flds == t._flds ) return 1;
    for( int i=0; i<_flds.length; i++ )
      if( !Util.eq(_flds[i]._fld,t._flds[i]._fld) || _flds[i]._access!=t._flds[i]._access )
        return 0;
    for( int i=0; i<_flds.length; i++ )
      if( _flds[i]._t!=t._flds[i]._t )
        return -1;              // Some not-pointer-equals child types, must do the full check
    return 1;                   // All child types are pointer-equals, so must be equals.
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
    for( int i=0; i<_flds.length; i++ ) {
      Type t0 =   _flds[i]._t;
      Type t1 = t._flds[i]._t;
      if( t0!=t1 &&                // Normally suffices to test ptr-equals only
          (t0==null || t1==null || // Happens when asserting on partially-built cyclic types
           !t0.cycle_equals(t1)) ) // Must do a full cycle-check
        return false;
    }
    return true;
  }

  static boolean isDigit(char c) { return '0' <= c && c <= '9'; }
  private boolean is_tup() {
    if( _flds.length<=1 ) return true;
    return isDigit(_flds[1]._fld.charAt(0));
  }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    // Special shortcut for the all-prims display type
    if( fld_find("!") != -1 && fld_find("math_pi") != -1 ) {
      Type t1 = _flds[1]._t;
      sb.p(t1 instanceof TypeFunPtr
           ? (((TypeFunPtr)t1)._fidxs.above_center() ? "PRIMS" : "LOW_PRIMS")
           : "PRIMS_"+t1);
    } else {
      boolean field_sep=false;
      for( int i=0; i<_flds.length; i++ ) {
        if( !debug && i==0 && Util.eq(_flds[0]._fld,"^") ) continue; // Do not print the ever-present display
        _flds[i].str(sb,dups,mem,debug); // Field name, access mod, type
        sb.p(is_tup ? ", " : "; ");      // Between fields
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
  private static TypeStruct FREE=null;
  private TypeStruct free( TypeStruct ret ) { _hash=0; _flds=null; _cyclic=false; FREE=this; return ret; }
  public  static TypeStruct malloc( String name, boolean any, TypeFld[] flds, boolean open ) {
    assert check_name(name);
    TypeStruct t1 = FREE == null ? new TypeStruct() : FREE;
    FREE = null;
    return t1.init(name, any,flds,open);
  }
  private TypeStruct hashcons_free() {
    _flds = TypeFlds.hash_cons(_flds);
    TypeStruct t2 = hashcons();
    return this==t2 ? this : free(t2);
  }

  // Make a collection of fields, with no display and all with default names and final fields.
  public static TypeFld[] flds(Type t1                  ) { return TypeFlds.ts(TypeFld.NO_DISP,TypeFld.make_arg(t1,1)); }
  public static TypeFld[] flds(Type t1, Type t2         ) { return TypeFlds.ts(TypeFld.NO_DISP,TypeFld.make_arg(t1,1), TypeFld.make_arg(t2,2)); }
  public static TypeFld[] tups(Type t1, Type t2         ) { return TypeFlds.ts(TypeFld.NO_DISP,TypeFld.make_tup(t1,1), TypeFld.make_tup(t2,2)); }
  public static TypeFld[] tups(Type t1, Type t2, Type t3) { return TypeFlds.ts(TypeFld.NO_DISP,TypeFld.make_tup(t1,1), TypeFld.make_tup(t2,2), TypeFld.make_tup(t3,3)); }

  // Make a display field and a specific named field
  public static TypeStruct make( String fld_name, Type t ) { return make(fld_name,t,Access.Final); }
  public static TypeStruct make( String fld_name, Type t, Access a ) { return make(TypeFlds.ts(TypeFld.NO_DISP,TypeFld.make(fld_name,t,a,1))); }
  // Make using the fields, with no struct name, low and closed; typical for a
  // well-known structure.  Make auto-allocate a TypeFld[], if not already
  // allocated - which is a perf-hit in high usage points.  Typically used this
  // way in tests.
  public static TypeStruct make( TypeFld... flds ) { return make("",false,flds,false); }
  // Make auto-allocate a TypeFld[], if not already allocated - which is a
  // perf-hit in high usage points.  Typically used this way in tests.
  public static TypeStruct make( Type... ts ) {
    TypeFld[] flds = TypeFlds.get(ts.length+1);
    flds[0]=TypeFld.NO_DISP;
    for( int i=0; i<ts.length; i++ )
      flds[i+1] = TypeFld.make(TypeFld.fldBot,ts[i],i+1);
    return make("",false,flds,false);
  }
  // Malloc/hashcons in one pass
  public static TypeStruct make( String name, boolean any, TypeFld[] flds, boolean open ) { return malloc(name,any,flds,open).hashcons_free(); }

  // Make an "open" struct with an initial display field.
  public static TypeStruct open(Type tdisp) { return make("",false,TypeFlds.ts(TypeFld.make_tup(tdisp,0)),true); }
  // Make a closed struct from an open one
  public TypeStruct close() { assert _open; return malloc(_name,_any,_flds,false).hashcons_free(); } // Mark as no-more-fields

  // Make a named TypeStruct from an unnamed one
  public TypeStruct make_from( String name ) { return malloc(name,_any,_flds,_open).hashcons_free();  }
  // Make a TypeStruct with all new fields
  public TypeStruct make_from( TypeFld[] flds ) { return malloc(_name,_any,flds,_open).hashcons_free();  }

  @Override boolean is_display() {
    return
      this==TypeMemPtr.DISPLAY || this==TypeMemPtr.DISPLAY._dual ||
        (_flds.length >= 1 && _flds[0].is_display_ptr());
  }

  // The lattice extreme values
  public  static final TypeStruct ANYSTRUCT = make("",true ,new TypeFld[0],false);
  public  static final TypeStruct ALLSTRUCT = make("",false,new TypeFld[0],true );

  // A bunch of types for tests
  public  static final TypeStruct POINT = make(flds(TypeFlt.FLT64,TypeFlt.FLT64));
  public  static final TypeStruct NAMEPT= make("Point:",false,POINT._flds,false);
          static final TypeStruct TFLT64= make(".",TypeFlt.FLT64); //  (  flt)
  public  static final TypeStruct A     = make("a",TypeFlt.FLT64);
  private static final TypeStruct C0    = make("c",TypeInt.FALSE); // @{c:0}
  private static final TypeStruct D1    = make("d",TypeInt.TRUE ); // @{d:1}
  public  static final TypeStruct ARW   = make("a",TypeFlt.FLT64,Access.RW);
  public  static final TypeStruct FLT64 = make(flds(TypeFlt.FLT64)); // {flt->flt}
  public  static final TypeStruct INT64_INT64= make(flds(TypeInt.INT64,TypeInt.INT64)); // {int int->int }

  // Pile of sample structs for testing
  static final TypeStruct[] TYPES = new TypeStruct[]{ALLSTRUCT,POINT,NAMEPT,A,C0,D1,ARW,INT64_INT64};

  // Dual the flds, dual the tuple.
  @Override protected TypeStruct xdual() {
    TypeFld[] flds = TypeFlds.get(_flds.length);
    for( int i=0; i<_flds.length; i++ ) flds[i] = _flds[i].dual();
    return new TypeStruct().init(_name,!_any,TypeFlds.hash_cons(flds),!_open);
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    if( _dual != null ) return _dual;
    // Clone the fields for the recursive dual, and grab the field duals
    TypeFld[] flds = TypeFlds.get(_flds.length);
    for( int i=0; i<_flds.length; i++ )
      // Some fields are interned already, the cyclic ones are not.
      flds[i] = _flds[i].interned() ? _flds[i]._dual : _flds[i].xdual();
    TypeStruct dual = _dual = new TypeStruct().init(_name,!_any,flds,!_open);
    if( _hash != 0 ) {
      assert _hash == compute_hash();
      dual._hash = dual.compute_hash(); // Compute hash before recursion
    }
    for( int i=0; i<_flds.length; i++ )
      flds[i] = _flds[i].interned() ? _flds[i]._dual : _flds[i].rdual();
    dual._flds = TypeFlds.hash_cons(flds); // hashcons cyclic arrays
    dual._dual = this;
    dual._cyclic = _cyclic;
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
    TypeStruct thsi = this;
    TypeStruct that = (TypeStruct)t;
    // INVARIANT: Both this and that are prior existing & interned.
    assert RECURSIVE_MEET > 0 || (thsi.interned() && that.interned());
    // INVARIANT: Both MEETS are empty at the start.  Nothing involved in a
    // potential cycle is interned until the Meet completes.
    assert RECURSIVE_MEET > 0 || (MEETS0.isEmpty());

    // If both are cyclic, we have to do the complicated cyclic-aware meet
    if( _cyclic && that._cyclic )
      return cyclic_meet(that);
    // Recursive but not cyclic; since at least one of these types is
    // non-cyclic normal recursion will bottom-out.

    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    return thsi._flds.length <= that._flds.length ? thsi.xmeet1(that,false) : that.xmeet1(thsi,false);
  }

  // Meet 2 structs, shorter is 'this'.
  private TypeStruct xmeet1( TypeStruct tmax, boolean is_loop ) {
    int len = _any ? tmax._flds.length : _flds.length;
    // Meet of common elements
    TypeFld[] flds = TypeFlds.get(len);
    for( int i=0; i<_flds.length; i++ )
      flds[i] = is_loop && flds[i]._access==Access.Final
        ? _flds[i]              // Ignore RHS on final fields around loops
        : _flds[i].xmeet(tmax._flds[i]); // Recursive not cyclic
    // Elements only in the longer tuple; the short struct must be high and so
    // is effectively infinitely extended with high fields.
    for( int i=_flds.length; i<len; i++ )
      flds[i] = tmax._flds[i];
    // Ignore name in the non-recursive meet, it will be computed by the outer
    // 'meet' call anyways.
    return malloc("",_any&tmax._any,flds,_open|tmax._open).hashcons_free();
  }

  // Recursive meet in progress.
  // Called during class-init.
  private static class TPair {
    TypeStruct _ts0, _ts1;
    private static TPair KEY = new TPair(null,null);
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
    mt = this._clone();
    TypeStruct mx = that;
    MEETS0.put(new TPair(this,that),mt);

    // Do a shallow MEET: meet of field names and _any and all things that can
    // be computed without the cycle.  _flds[]._t not filled in yet.
    int len = mt.len(mx); // Length depends on all the Structs Meet'ing here
    if( len != mt._flds.length )
      mt._flds = Arrays.copyOf(mt._flds, len);// escaped a _flds
    if( mt._any  && !mx._any ) mt._any = mt._use = false;
    if(!mt._open &&  mx._open) mt._open=true ;
    for( int i=0; i<len; i++ )
      mt._flds[i] = TypeFld.cmeet(mt._flds[i],i<mx._flds.length ? mx._flds[i] : null);
    mt._name = mt.mtname(mx,mt);
    mt._hash = mt.compute_hash(); // Compute hash now that fields and flags are set

    // Since the result is cyclic, we cannot test the cyclic parts for
    // pre-existence until the entire cycle is built.  We can't intern the
    // partially built parts, but we want to use the normal xmeet call - which
    // normally recursively interns.  Turn off interning with the global
    // RECURSIVE_MEET flag.
    RECURSIVE_MEET++;

    // For-all _ts edges do the Meet.  Some are not-recursive and mapped, some
    // are part of the cycle and mapped, some
    for( int i=0; i<len; i++ ) {
      Type lfi = i<this._flds.length ? this._flds[i]._t : null;
      Type rti = i<that._flds.length ? that._flds[i]._t : null;
      Type mti = (lfi==null) ? rti : (rti==null ? lfi : lfi.meet(rti));
      Type mtx = mt._flds[i]._t; // Prior value, perhaps updated recursively
      Type mts = mtx==null ? mti : mtx.meet(mti); // Meet again
      mt._flds[i].setX(mts);                      // Finally update
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
    mt = shrink(mt.reachable(),mt);
    Ary<Type> reaches = mt.reachable(); // Recompute reaches after shrink
    assert check_uf(reaches);
    UF.clear();
    RECURSIVE_MEET--;
    // This completes 'mt' as the Meet structure.
    return mt.install_cyclic(reaches);
  }

  // Install, cleanup and return
  public TypeStruct install_cyclic(Ary<Type> reachs) {
    // Check for dups.  If found, delete entire cycle, and return original.
    TypeStruct old = (TypeStruct)intern_lookup();
    // If the cycle already exists, just drop the new Type on the floor and let
    // GC get it and return the old Type.
    if( old == null ) {         // Not a dup
      mark_cyclic(get_cyclic(),reachs);
      assert !_cyclic || repeats_in_cycles()==null;
      rdual();               // Complete cyclic dual
      // Insert all members of the cycle into the hashcons.  If self-symmetric,
      // also replace entire cycle with self at each point.
      if( equals(_dual) ) throw AA.unimpl();
      walk( t -> {
          assert t._hash==0 || t._hash==t.compute_hash();
          if( t.interned() ) return false;
          if( t.retern() != t._dual ) t._dual.retern();
          return true;
        });

      assert _flds[0]._t.interned();
      old = this;
    }
    MEETS0.clear();
    return old;
  }

  // Test if this is a cyclic value (and should not be interned) with internal
  // repeats.  i.e., not a minimal cycle.
  TypeStruct repeats_in_cycles() {
    assert _cyclic;
    return repeats_in_cycles(this,new VBitSet());
  }
  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) {
    if( bs.tset(_uid) ) return null;
    if( this!=head && equals(head) ) return this;
    for( TypeFld t : _flds ) {
      TypeStruct ts = t.repeats_in_cycles(head,bs);
      if( ts!=null ) return ts;
    }
    return null;
  }

  // Shallow clone, not interned.  Fields are also cloned, but not deeper.
  private TypeStruct _clone() {
    assert interned();
    TypeFld[] flds = TypeFlds.clone(_flds); // Shallow field clone
    TypeStruct t = malloc(_name,_any,flds,_open);
    t._hash = t.compute_hash();
    return t;
  }

  // This is for a struct that has grown 'too deep', and needs to be
  // approximated to avoid infinite growth.
  public  static final NonBlockingHashMapLong<Type> UF = new NonBlockingHashMapLong<>();
  private static final IHashMap OLD2APX = new IHashMap();
  public TypeStruct approx( int cutoff, int alias ) {
    boolean shallow=true;
    for( TypeFld fld : _flds )
      if( fld._t._type == TMEMPTR ) { shallow=false; break; }
    if( shallow ) return this;  // Fast cutout for boring structs

    // Scan the old copy for elements that are too deep.
    // 'Meet' those into the clone at one layer up.
    RECURSIVE_MEET++;
    assert UF.isEmpty();
    assert OLD2APX.isEmpty();
    TypeStruct apx = ax_impl_struct( alias, true, cutoff, null, 0, this, this );
    // Remove any leftover internal duplication
    apx = shrink(apx.reachable(),apx);
    RECURSIVE_MEET--;
    TypeStruct rez = this;
    if( apx != this ) {
      Ary<Type> reaches = apx.reachable();
      assert check_uf(reaches);
      assert !check_interned(reaches);
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
    TypeStruct nts = (TypeStruct)old.clone();
    nts._flds  = TypeFlds.clone(old._flds);
    OLD2APX.put(old,nts);
    for( int i=0; i<old._flds.length; i++ ) // Fill clone with approximation
      if( old._flds[i]._t._type == TMEMPTR )
        nts._flds[i].setX(ax_impl_ptr (alias,cutoff,cutoffs,d,dold,(TypeMemPtr)old._flds[i]._t));
      else if( old._flds[i]._t._type == TFUNPTR )
        nts._flds[i].setX(ax_impl_fptr(alias,cutoff,cutoffs,d,dold,(TypeFunPtr)old._flds[i]._t));
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
    TypeMemPtr nmp = (TypeMemPtr)old.clone();
    OLD2APX.put(old,nmp);
    if( old._obj instanceof TypeStruct )
      nmp._obj = ax_impl_struct(alias,nmp._aliases.test(alias),cutoff,cutoffs,d,dold,(TypeStruct)old._obj);
    else if( old._obj == TypeObj.XOBJ || old._obj==nmp._obj )
      ; // No change to nmp._obj
    else if( old._obj == TypeObj.OBJ )
      nmp._obj = TypeObj.OBJ;   // Falls hard
    else
      throw com.cliffc.aa.AA.unimpl();
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
    TypeFunPtr nmp = (TypeFunPtr)old.clone();
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
    if( nt._hash != 0 && nt.interned() ) return nt.meet(old);
    assert nt._hash==0;         // Not definable yet
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
      // Compute a new target length.  Generally size is unchanged, but will
      // change if mixing structs.
      int len = ots.len(nts);     // New length
      if( len != nts._flds.length ) // Grow/shrink as needed
        nts._flds = Arrays.copyOf(nts._flds, len);
      int clen = Math.min(len,ots._flds.length);
      // Meet all the non-recursive parts
      nts._any &= ots._any ;  nts._use = nts._any;
      nts._open|= ots._open;
      for( int i=0; i<clen; i++ )
        nts._flds[i].cmeet(ots._flds[i]);
      // Now recursively do all common fields
      for( int i=0; i<clen; i++ )
        nts._flds[i].setX(ax_meet(bs,nts._flds[i]._t,ots._flds[i]._t));
      break;
    default: throw AA.unimpl();
    }
    return nt;
  }

  // Walk an existing, not-interned, structure.  Stop at any interned leaves.
  // Check for duplicating an interned Type or a UF hit, and use that instead.
  // Computes the final hash code.
  private static final IHashMap DUPS = new IHashMap();
  public static TypeStruct shrink( Ary<Type> reaches, TypeStruct tstart ) {
    assert DUPS.isEmpty();
    // Structs never change their hash based on field types.  Set their hash first.
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);
      if( t instanceof TypeStruct || t instanceof TypeFld )
        t._hash = t.compute_hash();
    }
    // TMPs depend on Structs
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);
      if( t instanceof TypeMemPtr )
        t._hash = t.compute_hash();
    }
    // TFPs depend on TMPS for display
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);
      if( t instanceof TypeFunPtr )
        t._hash = t.compute_hash();
    }

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
          for( int i=0; i<ts._flds.length; i++ ) {
            TypeFld tfld = ts._flds[i], tfld2 = ufind(tfld);
            if( tfld != tfld2 ) {
              progress = true;
              ts._flds[i] = tfld2;
            }
          }
          break;
        case TFLD:              // Update all TFlds
          TypeFld tfld = (TypeFld)t0;
          Type tft = tfld._t, t2 = ufind(tft);
          if( tft != t2 ) {
            progress = true;
            tfld.setX(t2);
          }
          break;

        default: break;
        }
        DUPS.put(t0);
      }
    }
    DUPS.clear();
    return ufind(tstart);
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
    assert lost._hash==0 || !lost.interned();
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

  // Reachable collection of TypeMemPtr and TypeStruct.
  // Optionally keep interned Types.  List is pre-order.
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
      case TSTRUCT:  for( TypeFld tf : ((TypeStruct)t)._flds ) push(work, tf); break;
      default: break;
      }
    }
    return work;
  }
  private void push( Ary<Type> work, Type t ) {
    int y = t._type;
    if( (y==TMEMPTR || y==TFUNPTR || y==TSTRUCT || y==TFLD) &&
        (t._hash == 0 || !t.interned()) && work.find(t)==-1 )
      work.push(t);
  }

  // Walk, looking for not-minimal.  Happens during 'approx' which might
  // require running several rounds of 'replace' to fold everything up.
  private static boolean check_uf(Ary<Type> reaches) {
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

  // Get BitSet of not-interned cyclic bits.  Almost classic cycle-finding
  // algorithm; since Structs have labeled out-edges (with field names), we can
  // have multiple output edges from the same node (struct) to the same
  // TypeMemPtr.  The classic cycle-finders do not work with multi-edges.
  private BitSet get_cyclic( ) {
    return get_cyclic(new BitSet(),new VBitSet(),new Ary<>(Type.class),this);
  }
  private static BitSet get_cyclic(BitSet bcs, VBitSet bs, Ary<Type> stack, Type t ) {
    if( t.interned() ) return bcs;
    if( bs.test(t._uid) ) {     // If visiting again... have found a cycle t->....->t
      // All on the stack are flagged as being part of a cycle
      int i;
      i=stack._len-1;
      while( i >= 0 && stack.at(i)!=t ) i--;
      if( i== -1 ) return bcs;  // Due to multi-edges, we might not find if dupped, so just ignore
      for( ; i < stack._len; i++ )
        bcs.set(stack.at(i)._uid);
      bcs.set(t._uid);
      return bcs;
    }
    stack.push(t);              // Push on stack, in case a cycle is found
    switch( t._type ) {
    case TMEMPTR: get_cyclic(bcs,bs,stack,((TypeMemPtr)t)._obj ); break;
    case TFUNPTR: get_cyclic(bcs,bs,stack,((TypeFunPtr)t)._disp); break;
    case TFLD   : get_cyclic(bcs,bs,stack,((TypeFld   )t)._t   ); break;
    case TSTRUCT: bs.set(t._uid); for( TypeFld fld : ((TypeStruct)t)._flds ) get_cyclic(bcs,bs,stack,fld); break;
    }
    stack.pop();                // Pop, not part of anothers cycle
    return bcs;
  }
  @SuppressWarnings("unchecked")
  private void mark_cyclic( BitSet bcs, Ary<Type> reaches ) {
    for( Type t : reaches ) {
      if( bcs.get(t._uid) ) {
        assert t.intern_lookup()==null; // Not interned
        t._dual=null;           // Remove any duals, so re-inserted clean
        if( t instanceof TypeStruct ) {
          TypeStruct ts = (TypeStruct)t;
          ts._cyclic = true;
          ts._flds = TypeFlds.hash_cons(ts._flds); // hashcons cyclic arrays
        }
      }
    }
  }

  // If unequal length; then if short is low it "wins" (result is short) else
  // short is high and it "loses" (result is long).
  private int len( TypeStruct tt ) { return _flds.length <= tt._flds.length ? len0(tt) : tt.len0(this); }
  private int len0( TypeStruct tmax ) { return _any ? tmax._flds.length : _flds.length; }


  // Buid a (recursively) sharpened pointer from memory.  Alias sets can be
  // looked-up directly in a map from BitsAlias to TypeObjs.  This is useful
  // for resolving all the deep pointer structures at a point in the program
  // (i.e., error checking arguments).  Given a TypeMem and a BitsAlias it
  // returns a TypeObj (and extends the HashMap for future calls).  The TypeObj
  // may contain deep pointers to other deep TypeObjs, including cyclic types.
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
    mt = shrink(mt.reachable(),mt); // No shrinking nor UF expected
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
    if( dull==NO_DISP || dull==NO_DISP.dual() ) { mem.sharput(dull,dull); return; }
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
    for( TypeFld fld : ((TypeStruct)t)._flds ) {
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
    for( TypeFld fld : ts._flds ) {
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
    TypeStruct dts2 = ((TypeStruct)dptr._obj)._clone();
    TypeMemPtr dptr2 = (TypeMemPtr)dptr.clone();
    dptr2._obj = dts2;  dptr2._hash = dptr2.compute_hash();
    dull_cache.put(dull._aliases,dptr2);
    // walk all fields, copy unless TMP.
    for( int i=0; i<dts2._flds.length; i++ ) {
      TypeFld dts2_fld = dts2._flds[i];
      Type t = dts2_fld._t;
      if( t instanceof TypeMemPtr ) // For TMP, recurse on dull pointers.
        dts2_fld.setX(_sharp(mem,((TypeMemPtr)t),dull_cache));
      if( t instanceof TypeFunPtr ) {
        TypeFunPtr tf = (TypeFunPtr) t;
        if( tf._disp instanceof TypeMemPtr ) { // Need  a pointer to sharpen
          TypeMemPtr dptr3 = _sharp(mem, (TypeMemPtr) tf._disp, dull_cache);
          dts2_fld.setX(dptr3.interned()             // Sharp return?
            ? tf.make_from(dptr3)        // Make sharp TFP field
            : tf._sharpen_clone(dptr3)); // Make dull  TFP field
        }
      }
      if( dts2_fld._t.interned() )
        dts2._flds[i] = dts2_fld.hashcons_free();
    }
    if( !_is_sharp(dts2) ) return dptr2; // Return the work-in-progress
    // Then copied field types are all sharp and interned.
    // Intern the fields themselves.
    for( int i=0; i<dts2._flds.length; i++ )
      if( !dts2._flds[i]._t.interned() )
        dts2._flds[i] = dts2._flds[i].hashcons_free();
    dull_cache.remove(dull._aliases);// Move the entry from dull cache to sharp cache
    TypeStruct sts = dts2.hashcons_free();
    return mem.sharput(dull,dull.make_from(sts));
  }

  @Override public Type meet_loop(Type t2) {
    if( this==t2 ) return this;
    if( !(t2 instanceof TypeStruct) ) return meet(t2);
    if( _flds.length != ((TypeStruct)t2)._flds.length ) return meet(t2);
    return xmeet1((TypeStruct)t2,true);
  }


  // Extend the current struct with a new named field
  public TypeStruct add_fld( String name, Access mutable ) { return add_fld(name,mutable,Type.SCALAR); }
  public TypeStruct add_fld( String name, Access mutable, Type tfld ) {
    assert name==null || Util.eq(name,TypeFld.fldBot) || fld_find(name)==-1;
    assert !_any && _open;
    TypeFld[] flds = TypeFlds.copyOf(_flds,_flds.length+1);
    flds[_flds.length] = TypeFld.make(name==null ? TypeFld.fldBot : name,tfld,mutable,_flds.length);
    return make(_name,_any,flds,true);
  }
  public TypeStruct set_fld( int i, Type t, Access ff ) {
    TypeFld[] flds = TypeFlds.copyOf(_flds,_flds.length);
    flds[i] = TypeFld.make(_flds[i]._fld,t,ff,_flds[i]._order);
    return make_from(flds);
  }

  // ------ Utilities -------
  // Return the index of the matching field (or nth tuple), or -1 if not found
  // or field-num out-of-bounds.
  public int fld_find( String fld ) {
    assert fld != TypeFld.fldTop && fld != TypeFld.fldBot;
    return TypeFld.fld_find(_flds,fld);
  }

  // Return type at field name
  @Override public Type fld(String fld) {
    int idx = fld_find(fld);
    return idx==-1 ? Type.ANY : _flds[idx]._t;
  }
  public TypeFld fld( int idx ) { return _flds[idx]; }

  public Type at( int idx ) { return _flds[idx]._t; }
  public Type last() { return _flds[_flds.length-1]._t; }
  public int len() { return _flds.length; }

  // Update (approximately) the current TypeObj.  Updates the named field.
  @Override public TypeStruct update(Access fin, String fld, Type val) { return update(fin,fld,val,false); }
  @Override public TypeStruct st    (Access fin, String fld, Type val) { return update(fin,fld,val,true ); }
  private TypeStruct update(Access fin, String fld, Type val, boolean precise) {
    int idx = fld_find(fld);
    if( idx == -1 ) return this; // Unknown field, assume changes no fields
    // Pointers & Memory to a Store can fall during GCP, and go from r/w to r/o
    // and the StoreNode output must remain monotonic.  This means store
    // updates are allowed to proceed even if in-error.
    if( fin==Access.Final || fin==Access.ReadOnly ) precise=false;
    Type   pval = precise ? val : _flds[idx]._t.meet(val);
    Access pfin = precise ? fin : _flds[idx]._access.meet(fin);
    TypeFld[] flds = TypeFlds.copyOf(_flds,_flds.length);
    flds[idx] = TypeFld.make(fld,pval,pfin,idx);
    return make(_name,_any,flds,_open);
  }

  // Keep the same basic type, and meet related fields.  Type error if basic
  // types are unrelated.
  @Override public TypeObj st_meet(TypeObj obj) {
    //if( !(obj instanceof TypeStruct) ) {
    //  if( obj.getClass()==TypeObj.class ) return obj.st_meet(this);
    //  throw unimpl(); // Probably type error from parser
    //}
    //TypeStruct trhs = (TypeStruct)obj;
    //if( trhs._ts.length < _ts.length ) throw com.cliffc.aa.AA.unimpl(); // Probably type error from parser
    //
    //Type[] ts = Types.clone(trhs._ts);
    //byte[] flags = trhs._flags.clone();
    //// Type error for mis-matched fields.  Meet common fields.
    //int len = _ts.length;
    //for( int i=0; i<trhs._ts.length; i++ ) {
    //  if( i<len && !Util.eq(_flds[i],trhs._flds[i]) )
    //    throw com.cliffc.aa.AA.unimpl(); // Probably type error from parser
    //  if( is_modifable(trhs.fmod(i)) ) {
    //    ts[i] = i<len ? trhs._ts[i].meet(_ts[i]) : ALL;
    //    flags(flags,i,i<len ? fmeet(flags(i),trhs.flags(i)) : FBOT);
    //  } // Else not modifiable, take RHS untouched
    //  assert ts[i].simple_ptr()==ts[i];
    //}
    //if( !(_name.isEmpty() || Util.eq(trhs._name,_name)) ) throw com.cliffc.aa.AA.unimpl(); // Need to meet names
    //// Note that "closed" is closed for all, same as lifting fields from a low struct.
    //return malloc(trhs._name,false,trhs._flds,ts,flags,trhs._open&_open).hashcons_free();
    throw unimpl();
  }

  @Override TypeObj flatten_fields() {
    TypeFld[] flds = TypeFlds.get(_flds.length);
    for( int i=0; i<_flds.length; i++ )
      flds[i] = _flds[i].make_from(Type.SCALAR,Access.bot());
    return make_from(flds);
  }

  // Used during liveness propagation from Loads.
  // Fields not-loaded are not-live.
  @Override TypeObj remove_other_flds(String fld, Type live) {
    int idx = fld_find(fld);
    if( idx == -1 ) return UNUSED; // No such field, so all fields will be XSCALAR so UNUSED instead
    TypeFld[] flds = TypeFlds.clone(_flds);
    for( int i=0; i<_flds.length; i++ ) {
      if( i != idx ) flds[i] = flds[i].setX(XSCALAR,Access.bot());
      flds[i] = flds[i].hashcons_free();
    }
    return make_from(flds);
  }

  boolean any_modifiable() {
    //if( _open ) return true;
    //for( byte b : _flags )
    //  if( is_modifable(fmod(b)) )
    //    return true;
    //return false;
    throw unimpl();
  }

  // Widen (lose info), to make it suitable as the default function memory.
  // All fields are widened to ALL (assuming a future error Store); field flags
  // set to bottom; only the field names are kept.
  @Override public TypeStruct crush() {
    if( _any ) return this;     // No crush on high structs
    TypeFld[] flds = TypeFlds.get(_flds.length);
    // Keep only the display pointer, as it cannot be stomped even with error code
    if( _flds.length>0 && _flds[0].is_display_ptr() )
      flds[0] = _flds[0].simple_ptr();
    for( int i=1; i<_flds.length; i++ ) { // Widen all fields, as-if crushed by errors, even finals.
      // Keep the name and field names untouched.
      TypeFld fld = _flds[i];
      flds[i] = TypeFld.make(fld._fld,Type.ALL,Access.bot(),fld._order);
    }
    // Low input so low output.
    return make_from(flds);
  }
  // Keep field names and orders.  Widen all field contents, including finals.
  @Override public TypeStruct widen() {
    boolean widen=false;
    for( TypeFld fld : _flds )
      if( fld._t.widen()!=fld._t )
        { widen=true; break; }
    if( !widen ) return this;
    TypeFld[] flds = TypeFlds.clone(_flds);
    for( int i=0; i<_flds.length; i++ )
      flds[i] = flds[i].setX(_flds[i]._t.widen()).hashcons_free();
    return make_from(flds);
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
    for( TypeFld fld : _flds ) if( fld._t==t || fld._t.contains(t,bs) ) return true;
    return false;
  }

  @Override public void walk( Predicate<Type> p ) {
    if( p.test(this) )
      for( TypeFld fld : _flds ) fld.walk(p);
  }

  @Override public TypeStruct make_from(Type head, TypeMem mem, VBitSet visit) {
    if( visit.tset(_uid) ) return null;
    TypeFld[] flds = TypeFlds.clone(_flds);
    for( int i=0; i<flds.length; i++ )
      flds[i] = flds[i].make_from(head,mem,visit);
    return make_from(flds);
  }
}
