package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Consumer;
import java.util.function.Predicate;

/** A memory-based Tuple with optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.  Fields
 *  can be indexed by field name or numeric constant (i.e. tuples), but NOT by
 *  a general number - thats an Array.
 *
 *  The recursive type poses some interesting challenges.  It is represented as
 *  literally a cycle of pointers which must include a TypeStruct (and not a
 *  TypeTuple which only roots Types).  Type inference involves finding the
 *  Meet of two cyclic structures.  The cycles will not generally be of the
 *  same length.  However, each field Meets independently (and fields in one
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
  // Fields are named in-order and aligned with the Tuple values.  Field names
  // are never null, and never zero-length.  If the 1st char is a '^' the field
  // is Top; a '.' is Bot; all other values are valid field names.
  public @NotNull String @NotNull[] _flds;  // The field names
  public Type[] _ts;            // Matching field types
  public byte[] _finals;        // Fields that are final; 1==read-only, 0=r/w
  private BitsAlias _news;      // NewNode aliases that make this type
  private TypeStruct _uf;       // Tarjan Union-Find, used during cyclic meet
  private TypeStruct     ( boolean any, String[] flds, Type[] ts, byte[] finals, BitsAlias news) { super(TSTRUCT, any); init(any,flds,ts,finals,news); }
  private TypeStruct init( boolean any, String[] flds, Type[] ts, byte[] finals, BitsAlias news) {
    super.init(TSTRUCT, any);
    _flds  = flds;
    _ts    = ts;
    _finals= finals;
    _news  = news;
    _uf    = null;
    return this;
  }
  // Precomputed hash code.  Note that it can NOT depend on the field types -
  // because during recursive construction the types are not available.
  @Override int compute_hash() {
    int hash = super.compute_hash() + _news.hashCode();
    for( int i=0; i<_flds.length; i++ ) hash += _flds[i].hashCode()+_finals[i];
    return hash;
  }

  private static final Ary<TypeStruct> CYCLES = new Ary<>(new TypeStruct[0]);
  private TypeStruct find_other() {
    int idx = CYCLES.find(this);
    return idx != -1 ? CYCLES.at(idx^1) : null;
  }

  // Returns 1 for definitely equals, 0 for definitely unequals, and -1 if
  // needing the cyclic test.
  private int cmp( TypeStruct t ) {
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return 0;
    if( _news == t._news && _ts == t._ts && _flds == t._flds && _finals == t._finals ) return 1;
    for( int i=0; i<_ts.length; i++ )
      if( !_flds[i].equals(t._flds[i]) || _finals[i]!=t._finals[i] )
        return 0;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] )
        return -1;              // Some not-pointer-equals child types, must do the full check
    return 1;                   // All child types are pointer-equals, so must be equals.
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    int x = cmp(t);
    if( x != -1 ) return x == 1;
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
    int x = cmp(t);
    if( x != -1 ) return x == 1;

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
  TypeStruct repeats_in_cycles() {
    assert _cyclic;
    assert _uf == null;         // Not collapsing
    return repeats_in_cycles(this,new VBitSet());
  }
  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) {
    if( bs.tset(_uid) ) return null;
    assert _uf == null;         // Not collapsing
    if( this!=head && equals(head) ) return this;
    for( Type t : _ts ) {
      TypeStruct ts = t.repeats_in_cycles(head,bs);
      if( ts!=null ) return ts;
    }
    return null;
  }

  String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle

    SB sb = new SB();
    if( _uf!=null ) return "=>"+_uf;
    if( _any ) sb.p('~');
    boolean is_tup = _flds.length==0 || fldTop(_flds[0]) || fldBot(_flds[0]);
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{');
    for( int i=0; i<_flds.length; i++ ) {
      if( !is_tup ) sb.p(_flds[i]);
      Type t = at(i);
      if( !is_tup && t != SCALAR ) sb.p(_finals[i]==0 ? ":=" : "=");
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else if( t instanceof TypeMemPtr ) sb.p("*"+((TypeMemPtr)t)._aliases); // Do not recurse here, gets too big too fast
      else sb.p(t.str(dups));   // Recursively print field type
      if( i<_flds.length-1 ) sb.p(',');
    }
    sb.p(!is_tup ? '}' : ')');
    return sb.toString();
  }
  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle

    if( _uf!=null ) return _uf.dstr(sb.p("=>"),dups);
    if( _any ) sb.p('~');
    boolean is_tup = _flds.length==0 || fldTop(_flds[0]) || fldBot(_flds[0]);
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{').nl().ii(1); // open struct, newline, increase_indent
    for( int i=0; i<_flds.length; i++ ) {
      sb.i();                   // indent, 1 field per line
      if( !is_tup ) sb.p(_flds[i]);
      Type t = at(i);
      if( !is_tup && t != SCALAR ) sb.p(_finals[i]==0 ? ":=" : "=");
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else t.dstr(sb,dups);     // Recursively print field type
      if( i<_flds.length-1 ) sb.p(',');
      sb.nl();                  // one field per line
    }
    return sb.di(1).i().p(!is_tup ? '}' : ')');
  }

  // Unlike other types, TypeStruct never makes dups - instead it might make
  // cyclic types for which a DAG-like bottom-up-remove-dups approach cannot work.
  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  static TypeStruct malloc( boolean any, String[] flds, Type[] ts, byte[] finals, BitsAlias news ) {
    if( FREE == null ) return new TypeStruct(any,flds,ts,finals,news);
    TypeStruct t1 = FREE;  FREE = null;
    return t1.init(any,flds,ts,finals,news);
  }
  private TypeStruct hashcons_free() { TypeStruct t2 = (TypeStruct)hashcons();  return this==t2 ? this : free(t2);  }

  // Default tuple field names - all bottom-field names
  private static final String[] FLD0={};
  private static final String[] FLD1={"."};
  private static final String[] FLD2={".","."};
  private static final String[] FLD3={".",".","."};
  private static final String[][] FLDS={FLD0,FLD1,FLD2,FLD3};
          static String[] FLDS( int len ) { return FLDS[len]; }
  private static String[] flds(String... fs) { return fs; }
  public  static Type[] ts(Type... ts) { return ts; }
  private static Type[] ts(int n) { Type[] ts = new Type[n]; Arrays.fill(ts,SCALAR); return ts; }
  public  static byte[] bs(Type[] ts) { byte[] bs = new byte[ts.length]; Arrays.fill(bs,(byte)1); return bs; } // All read-only
  public  static TypeStruct make(         Type... ts) { return make(BitsAlias.REC,ts); }
  public  static TypeStruct make(int nnn, Type... ts) { return malloc(false,FLDS[ts.length],ts,bs(ts),BitsAlias.make0(nnn)).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type... ts) { return malloc(false,flds,ts,bs(ts),BitsAlias.RECBITS).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type[] ts, byte[] finals) { return malloc(false,flds,ts,finals,BitsAlias.RECBITS).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type[] ts, byte[] finals, BitsAlias news) { return malloc(false,flds,ts,finals,news).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type[] ts, byte[] finals, int nnn) { return malloc(false,flds,ts,finals,BitsAlias.make0(nnn)).hashcons_free(); }
  public  static TypeStruct make( int x ) { return make(ts(x)); }
  public  static TypeStruct make(String[] flds, byte[] finals) { return make(flds,ts(flds.length),finals); }

  public  static final TypeStruct POINT = make(flds("x","y"),ts(TypeFlt.FLT64,TypeFlt.FLT64));
          static final TypeStruct X     = make(flds("x"),ts(TypeFlt.FLT64 )); // @{x:flt}
          static final TypeStruct TFLT64= make(          ts(TypeFlt.FLT64 )); //  (  flt)
  public  static final TypeStruct A     = make(flds("a"),ts(TypeFlt.FLT64 ));
  private static final TypeStruct C0    = make(flds("c"),ts(TypeInt.FALSE )); // @{c:0}
  private static final TypeStruct D1    = make(flds("d"),ts(TypeInt.TRUE  )); // @{d:1}
  private static final TypeStruct ARW   = make(flds("a"),ts(TypeFlt.FLT64),new byte[1]);
  public  static final TypeStruct GENERIC = malloc(true,FLD0,new Type[0],new byte[0],BitsAlias.RECBITS).hashcons_free();
          static final TypeStruct ALLSTRUCT = make();

  // Recursive meet in progress
  private static final HashMap<TypeStruct,TypeStruct> MEETS1 = new HashMap<>(), MEETS2 = new HashMap<>();

  static final TypeStruct[] TYPES = new TypeStruct[]{ALLSTRUCT,POINT,X,A,C0,D1,ARW};

  // Dual the flds, dual the tuple.
  @Override protected TypeStruct xdual() {
    String[] as = new String[_flds.length];
    Type  [] ts = new Type  [_ts  .length];
    byte  [] bs = new byte  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_flds[i]);
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].dual();
    for( int i=0; i<bs.length; i++ ) bs[i] = (byte)(_finals[i]^1);
    return new TypeStruct(!_any,as,ts,bs,_news.dual());
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    if( _dual != null ) return _dual;
    String[] as = new String[_flds.length];
    Type  [] ts = new Type  [_ts  .length];
    byte  [] bs = new byte  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_flds[i]);
    for( int i=0; i<bs.length; i++ ) bs[i] = (byte)(_finals[i]^1);
    TypeStruct dual = _dual = new TypeStruct(!_any,as,ts,bs,_news.dual());
    dual._hash = dual.compute_hash(); // Compute hash before recursion
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].rdual();
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
    case TNAME:  return t.xmeet(this); // Let other side decide
    case TSTR:   return OBJ;
    case TOBJ:   return t.above_center() ? this : t;
    case TFLT:
    case TINT:
    case TNIL:
    case TTUPLE :
    case TFUNPTR:
    case TMEMPTR:
    case TRPC:
    case TFUN:
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
    byte  [] bs = new byte  [len];
    for( int i=0; i<_ts.length; i++ ) {
      as[i] = smeet(_flds[i],tmax._flds[i]);
      ts[i] =    _ts[i].meet(tmax._ts  [i]); // Recursive not cyclic
      bs[i] = (byte)(_finals[i]|tmax._finals[i]);
    }
    // Elements only in the longer tuple
    for( int i=_ts.length; i<len; i++ ) {
      as[i] = tmax._flds  [i];
      ts[i] = tmax._ts    [i];
      bs[i] = tmax._finals[i];
    }
    return malloc(_any&tmax._any,as,ts,bs,_news.meet(tmax._news)).hashcons_free();
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
      mt._flds  = Arrays.copyOf(mt._flds  , len);
      mt._ts    = Arrays.copyOf(mt._ts    , len);
      mt._finals= Arrays.copyOf(mt._finals, len);
    }
    if( mt._any && !mx._any ) mt._any=false;
    len = Math.min(len,mx._ts.length);
    for( int i=0; i<len; i++ ) {
      mt._flds[i] = smeet(mt._flds[i],mx._flds[i]); // Set the Meet of field names
      mt._finals[i] |= mx._finals[i];
    }
    mt._news = mt._news.meet(mx._news);
    mt._hash = mt.compute_hash(); // Compute hash now that fields and finals are set

    // Since the result is cyclic, we cannot test the cyclic parts for
    // pre-existence until the entire cycle is built.  We can't intern the
    // partially built parts, but we want to use the normal xmeet call - which
    // normally recursively interns.  Turn off interning with the global
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

    // Check for repeats right now
    for( TypeStruct ts : MEETS1.values() )
      if( ts!=mt && ts.equals(mt) )
        { mt.union(ts); mt = ts; break; } // Union together

    // Lower recursive-meet flag.  At this point the Meet 'mt' is still
    // speculative and not interned.
    if( --RECURSIVE_MEET > 0 )
      return mt;                // And, if not yet done, just exit with it

    // Remove any final UF before installation.
    // Do not install until the cycle is complete.
    RECURSIVE_MEET++;
    Ary<Type> reaches;
    while( check_uf(reaches = mt.reachable()) )
      mt = (TypeStruct)shrink( new HashMap<>(), mt );
    RECURSIVE_MEET--;
    // This completes 'mt' as the Meet structure.
    return mt.install_cyclic(reaches);
  }

  // Install, cleanup and return
  TypeStruct install_cyclic(Ary<Type> reachs) {
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
    Arrays.fill(ts,Type.ANY);
    TypeStruct tstr = malloc(_any,_flds.clone(),ts,_finals.clone(),_news);
    tstr._cyclic = true;
    return tstr;
  }

  // Tarjan Union-Find to help build cyclic structures
  private void union( TypeStruct tt) {
    assert !interned() ;
    assert _uf==null && tt._uf==null;
    if( this!=tt )
      _uf = tt;
  }
  private TypeStruct ufind() {
    TypeStruct u = _uf;
    if( u==null ) return this;
    while( u._uf != null ) u = u._uf;
    TypeStruct t = this;
    while( t != u ) { TypeStruct tmp = t._uf; t._uf = u; t=tmp; }
    return u;
  }

  // This is for a struct that has grown 'too deep', and needs to be
  // approximated to avoid infinite growth.
  public TypeStruct approx( int cutoff ) {
    int alias = _news.getbit();   // Must only be 1 alias at top level
    RECURSIVE_MEET++;
    HashMap<Type,Type> old2apx = new HashMap<>();
    copy(old2apx,this);

    // Scan the old copy for elements that are too deep.
    // 'Meet' those into the clone at one layer up.
    ax_impl( old2apx, new VBitSet(), alias, cutoff, 0, this, this );

    TypeStruct apx = (TypeStruct)old2apx.get(this);
    Ary<Type> reaches;
    while( check_uf(reaches = apx.reachable()) )
      apx = (TypeStruct)shrink( new HashMap<>(), apx );
    RECURSIVE_MEET--;
    assert !check_interned(reaches);
    return apx.install_cyclic(reaches);
  }

  private static void ax_impl( HashMap<Type,Type> old2apx, VBitSet bs, int alias, int cutoff, int d, TypeStruct dold, Type old ) {
    if( bs.tset(old._uid) ) return; // Been there, done that
    assert old.interned();

    // Walk internal structure, meeting into the approximation
    switch( old._type ) {
    case TNAME  : ax_impl(old2apx,bs,alias,cutoff,d,dold,((TypeName  )old)._t  ); break;
    case TMEMPTR: ax_impl(old2apx,bs,alias,cutoff,d,dold,((TypeMemPtr)old)._obj); break;
    case TSTRUCT:
      TypeStruct ts = (TypeStruct)old;
      if( ts._news.test(alias) ) { // Depth-increasing struct?
        if( d==cutoff ) {          // Cannot increase depth any more
          TypeStruct nts = ((TypeStruct)old2apx.get(dold)).ufind();
          TypeStruct xts = ((TypeStruct)old2apx.get( old)).ufind();
          xts.union(nts);
          old2apx.put(dold,nts); // Update after ufind
          old2apx.put( old,nts); // Update after union
          ax_meet(new VBitSet(), nts,old);
          return;
        }
        d++;              // Increase depth
        dold = ts;        // And this is the last TypeStruct seen at this depth
      }
      for( int i=0; i<ts._ts.length; i++ )
        ax_impl(old2apx,bs,alias,cutoff,d,dold,ts._ts[i]);
      break;
    }
  }
  // Update-in-place 'meet' of pre-allocated new types.  Walk all the old type
  // and meet into the corresponding new type.
  private static void ax_meet( VBitSet bs, Type t, Type old ) {
    assert old.interned() && !t.interned();
    // TODO: Flip switch to switch on 't' not 'old', moves NIL case into TMEMPTR.
    // TODO: Make a non-recursive "meet into".
    // Meet old into t
    switch( old._type ) {
    case TNIL: {
      if( !(t instanceof TypeMemPtr) ) throw AA.unimpl();
      TypeMemPtr nptr = (TypeMemPtr)t;
      nptr._aliases = nptr._aliases.meet_nil();
      break;
    }
    case TSCALAR:
      if( !(t instanceof TypeMemPtr) ) throw AA.unimpl();
      // TODO: Really begs for UF on all Types
      throw AA.unimpl(); // Update nptr to a SCALAR and chop the link
    case TNAME: {
      if( bs.tset(old._uid) ) return; // Been there, done that
      if( !(t instanceof TypeName) ) throw AA.unimpl();
      TypeName n = (TypeName)old, nn = (TypeName)t;
      if( !(n._name.equals(nn._name) &&
            n._depth==nn._depth &&
            n._lex==nn._lex) )
        throw AA.unimpl();
      Type nto = nn._t;
      if( nto instanceof TypeStruct ) nn._t = nto = ((TypeStruct)nto).ufind();
      if( nto.interned() ) nn._t = nto.meet(n._t);
      else ax_meet(bs,nto,n._t);
      break;
    }
    case TMEMPTR: {
      if( bs.tset(old._uid) ) return; // Been there, done that
      if( !(t instanceof TypeMemPtr) ) throw AA.unimpl();
      TypeMemPtr ptr = (TypeMemPtr)old, nptr = (TypeMemPtr)t;
      nptr._aliases = nptr._aliases.meet(ptr._aliases);
      TypeObj nto = nptr._obj;
      if( nto instanceof TypeStruct ) nptr._obj = nto = ((TypeStruct)nto).ufind();
      if( nto.interned() ) nptr._obj = (TypeObj)nto.meet(ptr._obj);
      else ax_meet(bs,nto,ptr._obj);
      break;
    }
    case TSTRUCT:
      if( bs.tset(old._uid) ) return; // Been there, done that
      if( !(t instanceof TypeStruct) ) throw AA.unimpl();
      TypeStruct ts = (TypeStruct)old, nts = (TypeStruct)t;
      assert nts._uf==null;     // Already handled by the caller
      // Meet all the non-recursive parts
      if( nts._ts.length != ts._ts.length ) throw AA.unimpl();
      nts._any &= ts._any;
      for( int i=0; i<ts._ts.length; i++ ) {
        nts._flds[i] = smeet(nts._flds[i],ts._flds[i]); // Set the Meet of field names
        nts._finals[i] |= ts._finals[i];
      }
      nts._news = nts._news.meet(ts._news);
      // Now recursively do all fields
      for( int i=0; i<ts._ts.length; i++ ) {
        Type  tf =  ts._ts[i];
        Type ntf = nts._ts[i];
        assert !(ntf instanceof TypeStruct);
        if( ntf.interned() ) nts._ts[i] = ntf.meet(tf);
        else ax_meet(bs,ntf,tf);
      }
      break;
    default: throw AA.unimpl();
    }
  }

  private Type copy(HashMap<Type,Type> old2apx, Type t ) {
    Type tn = old2apx.get(t);
    if( tn != null ) return tn; // Been there, done that

    switch( t._type ) {
    case TNAME  : {
      Type x = copy(old2apx,((TypeName)t)._t);
      tn = old2apx.get(t);
      if( tn == null )
        old2apx.put(t,tn = ((TypeName)t).make(x));
      break;
    }
    case TMEMPTR: {
      Type x = copy(old2apx,((TypeMemPtr)t)._obj);
      tn = old2apx.get(t);
      if( tn == null )
        old2apx.put(t,tn = ((TypeMemPtr)t).make((TypeObj)x));
      break;
    }
    case TSTRUCT:
      TypeStruct ts = (TypeStruct)t;
      tn = malloc(ts._any,ts._flds.clone(),new Type[ts._ts.length],ts._finals.clone(),ts._news);
      tn._hash = tn.compute_hash();
      old2apx.put(ts,tn);     // Put before recursive call
      for( int i=0; i<ts._ts.length; i++ )
        ((TypeStruct)tn)._ts[i] = copy(old2apx,ts._ts[i]);
      break;
    default: tn = t;            // Not part of the cycle
    }
    return tn;
  }

  private static Type shrink( HashMap<Type,Type> intern, Type old ) {
    assert !(old instanceof TypeStruct && ((TypeStruct)old)._uf != null);
    Type rez = old.intern_lookup();
    if( rez != null ) return rez; // Already have an interned version (which could be self)
    rez = intern.get(old);        // Been here, done that?
    if( rez != null ) return rez;


    // Walk internal structure, shrinking as you go
    switch( old._type ) {
    case TNAME: throw AA.unimpl();
    case TMEMPTR:
      TypeMemPtr nptr = (TypeMemPtr)old;
      TypeObj nto = nptr._obj;
      if( nto instanceof TypeStruct ) nptr._obj = nto = ((TypeStruct)nto).ufind();
      rez = ((TypeMemPtr)old).make((TypeObj)shrink(intern,nto));
      break;
    case TSTRUCT: {             // Structs must break cycles by installing early
      TypeStruct ts0 = (TypeStruct)old;
      ts0 = ts0.ufind();
      TypeStruct ts1 = (TypeStruct)intern.get(ts0); // Check for cyclic new stuff, and return it
      if( ts1 != null ) return ts1;
      ts1 = malloc(ts0._any,ts0._flds,new Type[ts0._ts.length],ts0._finals,ts0._news);
      ts1._hash = ts1.compute_hash();
      intern.put(ts0,ts1);  // Install before recursive call, so can hit on self
      // Build the complete (recursive) TypeStruct, with any previously interned children
      for( int i=0; i<ts0._ts.length; i++ )
        ts1._ts[i] = shrink(intern,ts0._ts[i]);
      rez = ts1;
      break;
    }
    default: return old;        // Not recursive, no need to clone
    }
    Type rez2 = intern.get(rez);
    if( rez2 != null ) return rez2;
    intern.put(old,rez);
    intern.put(rez,rez);
    return rez;
  }

  // Walk, looking for prior interned
  private static boolean check_interned(Ary<Type> reachs) {
    for( Type t : reachs )
      if( t.intern_lookup() != null )
        return true;
    return false;
  }

  // Reachable collection of TypeMemPtr, TypeName and TypeStruct.
  // Optionally keep interned Types.  List is pre-order.
  Ary<Type> reachable() {
    Ary<Type> work = new Ary<>(new Type[1],0);
    push(work, this);
    int idx=0;
    while( idx < work._len ) {
      Type t = work.at(idx++);
      switch( t._type ) {
      case TNAME:    push(work, ((TypeName  )t)._t  ); break;
      case TMEMPTR:  push(work, ((TypeMemPtr)t)._obj); break;
      case TSTRUCT:  for( Type tf : ((TypeStruct)t)._ts ) push(work, tf); break;
      default: break;
      }
    }
    return work;
  }
  private void push( Ary<Type> work, Type t ) {
    int y = t._type;
    if( (y==TNAME || y==TMEMPTR || y==TSTRUCT) &&
        !t.interned() && work.find(t)==-1 )
      work.push(t);
  }

  // Walk, looking for not-minimal.  Happens during 'approx' which might
  // require running several rounds of 'replace' to fold everything up.
  private static boolean check_uf(Ary<Type> reachs) {
    int err=0;
    HashMap<Type,Type> ss = new HashMap<>();
    for( Type t : reachs ) {
      Type tt;
      if( ss.get(t) != null || // Found unresolved dup; ts0.equals(ts1) but ts0!=ts1
          ((tt = t.intern_lookup()) != null && tt != t) ||
          (t instanceof TypeStruct && ((TypeStruct)t)._uf != null) ) // Found unresolved UF
        err++;
      ss.put(t,t);
    }
    return err != 0;
  }

  // Get BitSet of not-interned cyclic bits
  private BitSet get_cyclic( ) {
    return get_cyclic(new BitSet(),new VBitSet(),new Ary<>(Type.class),this);
  }
  private static BitSet get_cyclic(BitSet bcs, VBitSet bs, Ary<Type> stack, Type t ) {
    if( t.interned() ) return bcs;
    if( bs.tset(t._uid) ) {
      for( int i=stack.find(t); i>=0 && i<stack._len; i++ )
        bcs.set(stack.at(i)._uid);
      return bcs;
    }
    stack.push(t);
    switch( t._type ) {
    case TNAME:   get_cyclic(bcs,bs,stack,((TypeName  )t)._t  ); break;
    case TMEMPTR: get_cyclic(bcs,bs,stack,((TypeMemPtr)t)._obj); break;
    case TSTRUCT: for( Type tf : ((TypeStruct)t)._ts ) get_cyclic(bcs,bs,stack,tf); break;
    }
    stack.pop();
    return bcs;
  }
  private void mark_cyclic( BitSet bcs, Ary<Type> reachs ) {
    for( Type t : reachs )
      t._cyclic = bcs.get(t._uid);
  }

  // Build a mapping from types to their depth in a shortest-path walk from the
  // root.  Only counts depth on TypeStructs with the matching alias.
  HashMap<Type,Integer> depth(int alias) {
    HashMap<Type,Integer> ds = new HashMap<>();
    Ary<Type> t0 = new Ary<>(new Type[]{this});
    Ary<Type> t1 = new Ary<>(new Type[1],0);
    int d=0;                    // Current depth
    while( !t0.isEmpty() ) {
      while( !t0.isEmpty() ) {
        Type t = t0.pop();
        if( ds.get(t)!=null ) continue; // Been there, done that
        ds.put(t,d);            // Everything in t0 is in the current depth
        switch( t._type ) {
        case TNAME:    t0.push(((TypeName  )t)._t  ); break;
        case TMEMPTR:  t0.push(((TypeMemPtr)t)._obj); break;
        case TSTRUCT:
          TypeStruct ts = (TypeStruct)t;
          Ary<Type> tx = ts._news.test(alias) ? t1 : t0;
          for( Type tf : ts._ts ) tx.push(tf);
          break;
        default: break;
        }
      }
      Ary<Type> tmp = t0; t0 = t1; t1 = tmp; // Swap t0,t1
      d++;                                   // Raise depth
    }
    return ds;
  }

  static int max(int alias, HashMap<Type,Integer> ds) {
    int max = 0;
    for( Type t : ds.keySet() )
      if( filter(alias,t) )
        max = Math.max(max,ds.get(t));
    return max;
  }
  private static boolean filter( int alias, Type t ) {
    return (t instanceof TypeStruct) && ((TypeStruct)t)._news.test(alias);
  }


  // If unequal length; then if short is low it "wins" (result is short) else
  // short is high and it "loses" (result is long).
  private int len( TypeStruct tt ) { return _ts.length <= tt._ts.length ? len0(tt) : tt.len0(this); }
  private int len0( TypeStruct tmax ) { return _any ? tmax._ts.length : _ts.length; }

  static private boolean fldTop( String s ) { return s.charAt(0)=='^'; }
  static private boolean fldBot( String s ) { return s.charAt(0)=='.'; }
  // String meet
  private static String smeet( @NotNull String s0, @NotNull String s1 ) {
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

  // Return the index of the matching field (or nth tuple), or -1 if not found
  // or field-num out-of-bounds.
  public int find( String fld, int fld_num ) {
    if( fld==null )
      return fld_num < _ts.length ? fld_num : -1;
    for( int i=0; i<_flds.length; i++ )
      if( fld.equals(_flds[i]) )
        return i;
    return -1;
  }

  public Type at( int idx ) { return _ts[idx]; }

  // Update (approximately) the current TypeObj.  Updates the named field.
  @Override TypeObj update(byte fin, String fld, int fld_num, Type val) {
    assert val.isa_scalar();
    int idx = find(fld,fld_num);
    // No-such-field to update, so this is a program type-error.
    if( idx==-1 ) return ALLSTRUCT;
    // Update to a final field.  This is a program type-error
    if( _finals[idx] == 1 ) return this;
    byte[] finals = _finals;
    Type[] ts     = _ts;
    if( _finals[idx] != fin ) { finals = _finals.clone(); finals[idx] = fin; }
    if( _ts    [idx] != val ) { ts     = _ts    .clone(); ts    [idx] = val; }
    return malloc(_any,_flds,ts,finals,_news).hashcons_free();
  }
  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t.isa(this) ) return 0; // TODO: really: test same flds, each fld isBitShape
    if( t instanceof TypeName ) return 99; // Cannot pick up a name, requires user converts
    return 99;
  }
  // Build a depth-limited named type
  @Override TypeStruct make_recur(TypeName tn, int d, VBitSet bs ) {
    // Mid-construction recursive types are always self-type
    for( Type t : _ts )  if( t == null )  return this;
    boolean eq = true;
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ )
      eq &= (ts[i] = _ts[i].make_recur(tn,d,bs))==_ts[i];
    return eq ? this : make(_flds,ts);
  }

  // Mark if part of a cycle
  @Override void mark_cycle( Type head, VBitSet visit, BitSet cycle ) {
    if( visit.tset(_uid) ) return;
    if( this==head ) { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
    for( Type t : _ts ) {
      t.mark_cycle(head,visit,cycle);
      if( cycle.get(t._uid) )
        { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
    }
  }

  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { for( Type t : _ts) c.accept(t); }
  @Override public Type meet_nil() { return this; }

  @Override boolean contains( Type t, VBitSet bs ) {
    if( bs==null ) bs=new VBitSet();
    if( bs.get(_uid) ) return false;
    for( Type t2 : _ts) if( t2==t || t2.contains(t,bs) ) return true;
    return false;
  }
  @Override int depth( VBitSet bs ) {
    if( _cyclic ) return 9999;
    if( bs==null ) bs=new VBitSet();
    if( bs.get(_uid) ) return 0;
    int max=0;
    for( Type t : _ts) max = Math.max(max,t.depth(bs));
    return max+1;
  }
  @SuppressWarnings("unchecked")
  @Override void walk( Predicate<Type> p ) {
    if( p.test(this) )
      for( Type _t : _ts ) _t.walk(p);
  }
  // Keep the high parts
  @Override public TypeObj startype() {
    String[] as = new String[_flds.length];
    Type  [] ts = new Type  [_ts  .length];
    byte  [] bs = new byte  [_ts  .length]; // r-w is the high value
    for( int i=0; i<as.length; i++ ) as[i] = fldBot(_flds[i]) ? "^" : _flds[i];
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].above_center() ? _ts[i] : _ts[i].dual();
    return malloc(true,as,ts,bs,_news.dual()).hashcons_free();
  }
}
