package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.function.*;

import static com.cliffc.aa.AA.unimpl;

// Function indices or function pointers; a single instance can include all
// possible aliased function pointers.  Function pointers can be executed, are
// not GC'd, and cannot be Loaded or Stored through (although they can be
// loaded & stored).
//
// A function pointer includes a display (a back pointer to the enclosing
// environment); i.e. function pointers are "fat".  The display is typed as
// a TMP to a TypeStruct, or e.g. ANY (not live, nobody uses or cares or XNIL).
//
// The TFP indicates if it carries a display or not; a TFP without a display
// cannot be called and has to be bound to a display first.  An unbound TFP
// uses ANY.  For "static" functions, the display is bound to the prototype
// object immediately.
//
// Other arguments are not currently curried in the TFP itself, only nargs.
//
// Each function index (or fidx) is a constant value, a classic code pointer.
// Cloning the code immediately also splits the fidx with a new fidx bit for
// both the original and the new code.
//
public final class TypeFunPtr extends TypeNil<TypeFunPtr> implements Cyclic {
  // List of known functions in set, or 'flip' for choice-of-functions.
  // A single bit is a classic code pointer.

  // TODO: to support FIDX tracking with overloads, I allow meets of joins: any
  // given set of overloads represent a *join* of functions (choice).  Merging
  // such joins at Phis produces a meet-of-joins.

  // Many of the iterators over FIDXs do not (yet) distinguish meets vs joins,
  // and will have to be visited on a case-by-case basis.

  // Cannot just use a meet of overloaded functions, because as resolution
  // proceeds the set of functions shrinks not grows as Combo proceeds.  Thus
  // overloads are above-center, while Phi meets are below center.

  // Ponder data structure as
  // - local to TFP for now
  // - a BitsFun[], where the BitsFun are JOINs internally and MEET across.
  // - dual is BitsFun MEET internally and JOIN across?  dual uses _any bit.
  // - Zero length array is empty

  private BitsFun[] _fidxss;    // Known function bits

  private int _nargs;           // Number of formals, including the ctrl, mem, display
  public Type _ret;             // Return scalar type
  private Type _dsp;            // Display; often a TMP to a TS; ANY is dead (not live, nobody uses).

  private TypeFunPtr _init(BitsFun[] fidxss, int nargs, Type dsp, Type ret) {
    assert fidxss.length==0 || _any== fidxss[0].above_center();
    for( BitsFun fidxs : fidxss )
      assert fidxs!=BitsFun.EMPTY && _any==fidxs.above_center() && !fidxs.test(0);
    assert BitsFuns.interned(fidxss);
    assert !(dsp instanceof TypeFld);
    _fidxss = fidxss; _nargs=nargs; _dsp=dsp; _ret=ret;
    return this;
  }
  private TypeFunPtr init(boolean any, boolean nil, BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    super.init(any,nil);
    return _init(fidxss,nargs,dsp,ret);
  }
  private TypeFunPtr init(boolean any, boolean nil, boolean sub, BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    super.init(any,nil,sub);
    return _init(fidxss,nargs,dsp,ret);
  }
  @Override TypeFunPtr copy() { return _copy().init(_any,_nil,_sub,_fidxss,_nargs,_dsp,_ret); }
  @Override public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) { return reduce.apply(map.map(_dsp,"dsp"), map.map(_ret,"ret")); }
  @Override public long lwalk( LongStringFunc map, LongOp reduce ) { return reduce.run(map.run(_dsp,"dsp"), map.run(_ret,"ret")); }
  @Override public void walk( TypeStrRun map ) { map.run(_dsp,"dsp"); map.run(_ret,"ret"); }
  @Override public void walk_update( TypeMap map ) { _dsp = map.map(_dsp); _ret = map.map(_ret); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    TypeFunPtr tfp = (TypeFunPtr)t;
    Cyclic.Link dsplk = Cyclic._path_diff(_dsp,tfp._dsp,links);
    Cyclic.Link retlk = Cyclic._path_diff(_ret,tfp._ret,links);
    return Cyclic.Link.min(dsplk,retlk);
  }

  public boolean has_dsp() { return _dsp!=ALL; }
  public Type dsp() { return _dsp; }
  void set_dsp( Type dsp) { assert un_interned() && (has_dsp() || _dsp==dsp); _dsp = dsp; }

  // Static properties hashcode, no edge hashes
  @Override long static_hash() {
    long hash = 0;
    for( BitsFun fidxs : _fidxss ) hash ^= fidxs.hashCode();
    return Util.mix_hash(super.static_hash(),hash,_nargs^_dsp._type^_ret._type);
  }

  private boolean fxeq(TypeFunPtr t) {
    if( _fidxss == t._fidxss ) return true;
    if( _fidxss.length != t._fidxss.length ) return false;
    for( int i=0; i<_fidxss.length; i++ )
      if( _fidxss[i]!=t._fidxss[i] ) return false;
    return true;
  }
  // Static properties equals, no edges.  Already known to be the same class
  // and not-equals.
  @Override boolean static_eq(TypeFunPtr t) {
    return super.static_eq(t) && _nargs == t._nargs && _dsp._type == t._dsp._type && _ret._type == t._ret._type && fxeq(t);
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr tf) ) return false;
    return cycle_equals(tf);
  }

  private static final Ary<Type> CYCLES = new Ary<>(new Type[0]);
  private Type find_other() {
    int idx = CYCLES.find(this);
    return idx != -1 ? CYCLES.at(idx^1) : null;
  }

  // Structs can contain TFPs in fields and TFPs contain a Struct in a cycle.
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr tf) ) return false;
    if( !super.equals(tf) ) return false;
    if( !fxeq(tf) || _nargs != tf._nargs ) return false;
    if( _dsp!=tf._dsp && !_dsp.cycle_equals(tf._dsp) ) return false;
    if( _ret==tf._ret ) return true;
    if( _ret==null ) return false; // One if partially built, the other is fully built
    Type t2 =    find_other();
    if( t2 !=null ) return t2==tf  ; // Already in cycle report equals or not
    Type t3 = tf.find_other();
    if( t3 !=null ) return t3==this; // Already in cycle report equals or not

    int len = CYCLES._len;
    CYCLES.add(this).add(tf);
    boolean eq=_ret.cycle_equals(tf._ret);
    assert CYCLES._len==len+2;
    CYCLES._len=len;
    return eq;
  }

  @Override void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"X"+(char)('A'+ucnt._tfp++));
      return;
    }
    _dsp._str_dups(visit,dups,ucnt);
    _ret._str_dups(visit,dups,ucnt);
  }


  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    str_fidxs(sb);
    sb.p('{');                  // Arg list start
    if( debug ) _dsp._str(visit,dups, sb, true, indent).p(",");
    sb.p(_nargs).p(" ->");
    boolean ind = indent && _ret._str_complex(visit,dups);
    if( ind ) sb.nl().ii(1).i();
    _ret._str(visit,dups, sb, debug, indent).p(' ');
    if( ind ) sb.nl().di(1).i();
    return _str_nil(sb.p('}'));
  }

  @Override boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) { return _ret._str_complex(visit,dups); }

  // String print fancy fidxs
  public SB str_fidxs(SB sb) {
    assert _fidxss.length==1; // TODO: fix me!
    return _fidxss[0].str(sb);
  }

  static TypeFunPtr valueOf(Parse P, String cid) {
    BitsFun fidxs = P.bits(BitsFun.EMPTY);
    BitsFun[] fidxss = BitsFuns.make(fidxs);
    P.require('{');
    TypeFunPtr tfp = malloc(fidxss,0,null,null);
    if( cid!=null ) P._dups.put(cid,tfp);
    tfp.set_dsp(P.type());
    P.require(',');
    tfp._nargs = (int)P.num();
    P.require('-');  P.require('>');
    tfp._ret = P.type();
    P.require('}');
    return tfp;
  }


  static { new Pool(TFUNPTR,new TypeFunPtr()); }

  // Lambda/FunPtr transfer functions wrap a TFP/FIDX around a return, possibly
  // repeatedly and must monotonically reach a fixed point.  Doing this by
  // restricting to a single in the return chain is not monotonic:
  //
  //  INPUT           WRAP WITH 2 ->        APPROX
  // ~scalar     ==>> 2 -> ~scalar     ==>> 2   -> ~scalar
  // 2   -> 2  * ==>> 2 -> 2   -> 2  * ==>> 2   -> 2  *
  // 2,3 -> 2,3* ==>> 2 -> 2,3 -> 2,3* ==>> 2,3 -> 2,3*   \___ NOT MONOTONIC
  //  scalar     ==>> 2 ->  scalar     ==>> 2   ->  scalar/
  //
  // As the input falls from a ->2,3* cycle to scalar, the output (after
  // wrap-and-approximate) is not monotonic.


  private static final VBitSet CHK2 = new VBitSet();
  private static boolean check2(TypeFunPtr tfp) {
    // Make sure a FIDX appears only once, up to an ending self-cycle.
    CHK2.clear();
    while( tfp._ret!=tfp ) {      // Break if self-cycle, which can have anything
      for( BitsFun fidxs : tfp._fidxss )
        for( int fidx : fidxs ) if( CHK2.tset(fidx) ) return false;
      if( !(tfp._ret instanceof TypeFunPtr ret) ) break;
      tfp = ret;
    }
    return true;
  }

  // Functions can grow indefinitely, if being built in a recursive loop.
  // We check that fidx return invariant holds.
  public static TypeFunPtr make ( boolean any, boolean nil, boolean sub, BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    TypeFunPtr tfp = malloc(any, nil, sub, fidxss, nargs,dsp,ret).hashcons_free();
    assert check2(tfp);          // Assert new return-chain is valid
    return tfp;
  }

  // Assert the ret has the invariant.
  // Make the TFP, which might not have the invariant.
  // Call _rule2; the result has the invariant.
  // Check and return.
  public static TypeFunPtr makex( boolean any, boolean nil, boolean sub, BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    assert !(ret instanceof TypeFunPtr rtfp) || check2(rtfp); // Assert old return-chain is valid
    // Make the TFP, but it may NOT pass the invariant
    TypeFunPtr tfp = malloc(any, nil, sub, fidxss, nargs,dsp,ret).hashcons_free();
    CHK2.clear();
    TypeFunPtr tfp2 = tfp._rule2(fidxss,true); // Approx
    assert check2(tfp2);         // Assert new return-chain is valid
    return tfp2;
  }


  // Walk the ret chain recursively.
  // ApxRule: apx folds cycles from the ret-chain back to the front, until Rule2 holds.

  // This fails:
  // Rule1: fidxs appear in increasing sets (forces finite chain length)
  // (1)       b -> a  -> x
  // (2)       b -> ab -> ab*   // (1) isa (2)
  // Wrap with a->:
  // (1) a ->  b -> a  -> x
  // (2) a ->  b -> ab -> ab*   // (1) isa (2)
  // Approx the repeats of (a) in (1) (apply ApxRule until rule1 holds)
  // (1) a -> ab -> ab*
  // (2) a ->  b -> ab*   // FAILS MONOTONICITY


  // Rule2: fidxs appear once, and optionally in a final cycle
  // (1)      b -> a -> a,b*
  // (2)      b -> a -> Scalar   // (1) isa (2)
  // Wrap with a->:
  // (1) a -> b -> a -> a,b*
  // (2) a -> b -> a -> Scalar
  // Approx the repeats of (a) in (1) (apply ApxRule until rule2 holds)
  // (1) a -> b -> a,b -> a,b*
  // (2) a -> b -> a   -> Scalar  // FAILS MONOTONICITY
  // (3) a -> b -> Scalar // If end in a below-TFP, NO REPEATS....

  // Rule2: roll forwards and check that new_fidxs do not appear anywhere
  private TypeFunPtr _rule2(BitsFun[] new_fidxss, boolean first) {
    if( this==_ret ) return this; // Self-cycle, end is fine
    if( overlaps(new_fidxss,_fidxss) && !first )
      return _rule2_apx(); // Overlaps, so do hard approximation

    if( !(_ret instanceof TypeFunPtr rtfp) || rtfp==this )
      return this;              // End is fine, either self-cycle or a non-TFP

    TypeFunPtr tfp = rtfp._rule2(new_fidxss,false);
    if( tfp==_ret ) return this; // Return was fine, so i am fine
    if( tfp==null ) return make_from(_dsp,rtfp._ret); // Hard fail
    if( overlaps(new_fidxss,tfp._fidxss) ) return make_from(_dsp,tfp._ret);
    return make_from(_dsp,tfp);  // Wrap the return
  }

  private TypeFunPtr _rule2_apx() {
    if( this==_ret ) return this; // I am my own self-cycle
    if( !(_ret instanceof TypeFunPtr rtfp) ) { // make a self cycle
      if( _ret.isa(GENERIC_FUNPTR) )           // Falls to a cycle?
        return make_cycle(_any,_nil,_sub,_fidxss,_nargs,_dsp);
      return null;              // Hard fail, return low self
    }
    TypeFunPtr apx = rtfp._rule2_apx();
    if( apx==null ) return make_from(_dsp,rtfp._ret);
    // Fold my _fidxs into return cycle and return
    return make_cycle(_any,_nil,_sub,meet(_fidxss,apx._fidxss),_nargs,_dsp);
  }

  // Install a length-1 self-cycle
  static TypeFunPtr make_cycle( boolean any, boolean nil, boolean sub, BitsFun fidxs, int nargs, Type dsp ) {
    return make_cycle(any,nil,sub,BitsFuns.make(fidxs),nargs,dsp);
  }
  static TypeFunPtr make_cycle( boolean any, boolean nil, boolean sub, BitsFun[] fidxss, int nargs, Type dsp ) {
    TypeFunPtr tfp = malloc(any,nil,sub,fidxss,nargs,dsp,null);
    tfp._ret = tfp;             // Make a self-cycle of length 1
    assert dsp._hash!=0;        // Can be 'compute_hash'
    tfp._hash = tfp.compute_hash();
    TypeFunPtr old = (TypeFunPtr)tfp.intern_get(); // Intern check
    if( old!=null )                                // Return prior hit
      return POOLS[TFUNPTR].free(tfp,old);         // Return prior
    tfp._dual = tfp.xdual();                       // Install dual in a self-cycle
    tfp._dual._dual = tfp;
    tfp._dual._ret = tfp._dual;
    tfp._dual._hash = tfp._dual.compute_hash();
    return tfp.retern()._dual.retern().dual();     // Install self-cycle
  }

  // The original overlaps question is to provide a monotonic approximation for
  // functions returning functions.  Fidxss are expanded to include unions of
  // joins; I do not understand if this breaks the monotonicity.
  private static boolean overlaps( BitsFun[] f0ss, BitsFun[] f1ss ) {
    for( BitsFun fidx0s : f0ss )
      for( BitsFun fidx1s : f1ss )
        if( fidx0s.overlaps(fidx1s) )
          return true;
    return false;
  }
  private static BitsFun[] meet( BitsFun[] f0ss, BitsFun[] f1ss ) {
    if( f0ss.length==0 ) return f1ss;
    if( f1ss.length==0 ) return f0ss;
    if( f0ss.length!=f1ss.length ) throw unimpl();
    BitsFun[] fmss = BitsFuns.get(f0ss.length);
    for( int i=0; i<f0ss.length; i++ )
      fmss[i] = f0ss[i].meet(f1ss[i]);
    return fmss;
  }

  // Allocate and init
  private static TypeFunPtr malloc(boolean any, boolean nil, boolean sub, BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(any,nil,sub,BitsFuns.hash_cons(fidxss),nargs,dsp,ret);
  }
  private static TypeFunPtr malloc(BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    BitsFun fidxs0 = fidxss[0];
    assert !fidxs0.test(0);      // TODO: Fix side-effect, or intern
    fidxss[0] = fidxs0.clear(0); // Side-effects
    return t1.init(fidxs0.above_center(),fidxs0.test(0),fidxss,nargs,dsp,ret);
  }

  public static TypeFunPtr make ( BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    return make(BitsFuns.make(fidxs),nargs,dsp,ret);
  }
  public static TypeFunPtr make ( BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    boolean haz_nil = fidxss.length>0 && fidxss[0].test(0);
    boolean any = fidxss.length==0 || fidxss[0].above_center();
    boolean nil = any &&  haz_nil;
    boolean sub = any || !haz_nil;
    assert !haz_nil;             // TODO: Fix side-effect, or intern
    return make(any, nil, sub, fidxss,nargs,dsp,ret);
  }
  public static TypeFunPtr makex( BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    return makex(BitsFuns.make(fidxs),nargs,dsp,ret);
  }
  public static TypeFunPtr makex( BitsFun[] fidxss, int nargs, Type dsp, Type ret ) {
    boolean haz_nil = fidxss.length>0 && fidxss[0].test(0);
    boolean any = fidxss.length==0 || fidxss[0].above_center();
    boolean nil = any &&  haz_nil;
    boolean sub = any || !haz_nil;
    return makex(any, nil, sub, fidxss, nargs,dsp,ret);
  }
  public static TypeFunPtr make( int fidx, int nargs, Type dsp, Type ret ) {
    return make(BitsFun.make0(fidx),nargs,dsp,ret);
  }
  public static TypeFunPtr make_new_fidx( int parent, int nargs, Type dsp, Type ret ) {
    return make(BitsFun.make_new_fidx(parent),nargs,dsp,ret);
  }
  public static TypeFunPtr make( BitsFun fidxs, int nargs) {
    return make(fidxs,nargs,TypeMemPtr.NO_DISP,TypeNil.SCALAR);
  }
  public        TypeFunPtr make_from( Type dsp ) { return make(_fidxss,_nargs, dsp,_ret); }
  public        TypeFunPtr make_from( BitsFun fidxs  ) {
    throw unimpl();
    //return fidxss==_fidxss ? this : make( fidxss,_nargs,_dsp,_ret);
  }

  public        TypeFunPtr make_from( Type dsp, Type ret ) { return dsp==_dsp && ret==_ret ? this : make(_fidxss,_nargs, dsp,ret); }
  @Override TypeFunPtr make_from( boolean any, boolean nil, boolean sub ) {
    if( any == _any && nil == _nil && sub == _sub ) return this;
    return makex(any,nil,sub,_fidxss,_nargs,_dsp,_ret);
  }

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.NALL ,1,Type.ALL,Type.ALL);
  public  static final TypeFunPtr ARG2   =         make(BitsFun.NALL ,2,Type.ALL,Type.ALL);
  public  static final TypeFunPtr THUNK  = (TypeFunPtr)make(BitsFun.NALL ,3,Type.ALL,Type.ALL).meet(TypeNil.XNIL); // zero-arg function (plus ctrl, mem, display)
  public  static final TypeFunPtr EMPTY  =         make(new BitsFun[0],1,Type.ANY,Type.ANY);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,ARG2,THUNK};

  @Override protected TypeFunPtr xdual() {
    boolean xor = _nil == _sub;
    return malloc(!_any,_nil^xor,_sub^xor,BitsFuns.dual(_fidxss),-_nargs,_dsp.dual(),_ret.dual());
  }
  @Override void rdual() { _dual._dsp = _dsp._dual;  _dual._ret = _ret._dual; }

  @Override protected TypeFunPtr xmeet( Type t ) {
    TypeFunPtr tf = (TypeFunPtr)t;
    // Meet of nilable parts
    boolean any = _any & tf._any;
    boolean nil = _nil & tf._nil;
    boolean sub = _sub & tf._sub;
    // Meet of non-return parts
    BitsFun[] fidxss = meet(_fidxss,tf._fidxss);
    int nargs = (_nargs ^ tf._nargs) > 0 ? Math.min(_nargs,tf._nargs) : Math.max(_nargs,tf._nargs);
    Type dsp = _dsp.meet(tf._dsp);

    // If both are short cycles, the result is a short cycle
    if( _ret==this && tf._ret==tf )
      return make_cycle(any,nil,sub,fidxss,nargs,dsp);

    // Otherwise, recursively find the return
    Type ret = _ret.meet(tf._ret);

    return makex(any,nil,sub,fidxss,nargs,dsp,ret);
  }

  // All fidxs, whether meet or join
  public BitsFun fidxs() {
    if( _fidxss.length==0 ) return BitsFun.EMPTY;
    assert _fidxss.length==1;
    return _fidxss[0];
  }
  public int fidx() { return _fidxss[0].getbit(); } // Asserts internally single-bit
  public boolean is_fidx() { return _fidxss[0].abit() > 1; } // Single-bit TFP
  public boolean test(int fidx) {
    throw unimpl();
    //return _fidxss[0].test_recur(fidx);
  }
  public boolean is_empty() { return _fidxss.length==0; }
  public boolean is_full() {
    return _fidxss.length==1 && _fidxss[0]==BitsFun.NALL;
  }
  public int nargs() { return Math.abs(_nargs); }

  // Widens, not lowers.
  @Override public TypeFunPtr simple_ptr() {
    Type ds = _dsp.simple_ptr();
    Type rs = _ret.simple_ptr();
    if( _dsp==ds && _ret==rs ) return this;
    return make_from(ds,rs);
  }

  @Override public boolean is_con()       {
    // Constant display or unbound display
    return (!has_dsp() || _dsp.is_con()) &&
      // Single bit covers all functions (no new children added, but new splits
      // can appear).  Currently, not tracking this at the top-level, so instead
      // just triggering off of a simple heuristic: a single bit above BitsFun.ALL.
      is_fidx();
  }

  @Override public Type make_from(Type head, TypeMem map, VBitSet visit) {
    throw unimpl();
  }

  // All reaching fidxs, including any function returns
  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    //if( Type.ARF.tset(_uid) ) return _fidxs;
    //// Myself, plus any function returns
    //return _fidxs.meet(_ret._all_reaching_fidxs(tmem));
    throw unimpl();
  }

}
