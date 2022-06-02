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
  public BitsFun _fidxs;        // Known function bits
  private int _nargs;           // Number of formals, including the ctrl, mem, display
  public Type _ret;             // Return scalar type
  private Type _dsp;            // Display; often a TMP to a TS; ANY is dead (not live, nobody uses).

  private TypeFunPtr _init(BitsFun fidxs, int nargs, Type dsp, Type ret) {
    assert !fidxs.test(0); // No nil in fidxs, use nil/sub instead
    assert !(dsp instanceof TypeFld);
    _fidxs = fidxs; _nargs=nargs; _dsp=dsp; _ret=ret;
    return this;
  }
  private TypeFunPtr init(boolean any, boolean nil, BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    super.init(any,nil);
    return _init(fidxs,nargs,dsp,ret);
  }
  private TypeFunPtr init(boolean any, boolean nil, boolean sub, BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    super.init(any,nil,sub);
    return _init(fidxs,nargs,dsp,ret);
  }
  @Override TypeFunPtr copy() { return _copy().init(_any,_nil,_sub,_fidxs,_nargs,_dsp,_ret); }
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
  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_fidxs._hash,_nargs^_dsp._type^_ret._type); }

  // Static properties equals, no edges.  Already known to be the same class
  // and not-equals.
  @Override boolean static_eq(TypeFunPtr t) {
    return super.static_eq(t) && _fidxs == t._fidxs && _nargs == t._nargs && _dsp._type == t._dsp._type && _ret._type == t._ret._type;
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
    if( _fidxs!=tf._fidxs || _nargs != tf._nargs ) return false;
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
    _fidxs.str(sb);
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

  static TypeFunPtr valueOf(Parse P, String cid) {
    BitsFun fidxs = P.bits(BitsFun.EMPTY);
    P.require('{');
    TypeFunPtr tfp = malloc(fidxs,0,null,null);
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
  //  INPUT                   WRAP WITH [2]{->}               APPROX
  // ~scalar          ==>> [2]{-> ~scalar         } ==>> $[2  ]{->~scalar}
  // $[2  ]{->$[2  ]} ==>> [2]{-> $[2  ]{->$[2  ]}} ==>> $[2  ]{->$[2]   }
  // $[2,3]{->$[2,3]} ==>> [2]{-> $[2,3]{->$[2,3]}} ==>> $[2,3]{->$[2,3] } \___ NOT MONOTONIC
  // scalar           ==>> [2]{-> scalar          } ==>> $[2  ]{->scalar } /
  //
  // As the input falls from a $[2,3]{->$} cycle to scalar, the output (after
  // wrap-and-approximate) is not monotonic.

  // Invariant: the fidxes can appear in the return-chain only if they strictly
  // grow, otherwise we should have approximated.  This check stops at end end
  // or a matching fidx, but does not check after any match.
  private static boolean check(TypeFunPtr tfp) {
    // Scan for a dup or the cycle
    BitsFun fidxs = tfp._fidxs;
    while( tfp._ret instanceof TypeFunPtr ret ) {
      if( ret==tfp ) return true; // Found the ending cycle
      if( fidxs.isa(ret._fidxs) && fidxs!=ret._fidxs ) return true; // Strict increase in bits is OK
      if( fidxs.overlaps(ret._fidxs) )
        return false; // Partial overlap is NOT ok
      tfp = ret;
    }
    return true;
  }

  // Functions can grow indefinitely, if being built in a recursive loop.
  // We check that fidx return invariant holds.
  public static TypeFunPtr make ( boolean any, boolean nil, boolean sub, BitsFun fidxs, int nargs, Type dsp, Type ret ) { return _makex(any, nil, sub, fidxs,nargs,dsp,ret,false); }
  // Make and approximate an endlessly growing chain.
  public static TypeFunPtr makex( boolean any, boolean nil, boolean sub, BitsFun fidxs, int nargs, Type dsp, Type ret ) { return _makex(any, nil, sub, fidxs,nargs,dsp,ret,true ); }

  // Walk the TFP return chain.  If we find the end or a TFP with strictly
  // increasing fidxs, we can wrap and return.  If we have fidx overlap, but
  // not strictly increasing, we need to chop the TFP return chain here.
  private static TypeFunPtr _makex( boolean any, boolean nil, boolean sub, BitsFun fidxs, int nargs, Type dsp, Type ret, boolean apx ) {
    assert !(ret instanceof TypeFunPtr rtfp) || check(rtfp);
    TypeFunPtr tfp = malloc(any, nil, sub, fidxs,nargs,dsp,ret).hashcons_free();
    TypeFunPtr tfp2 = apx ? tfp._makex( fidxs) : tfp;
    assert check(tfp2);
    return tfp2;
  }

  // Walk to the end, looking for the need to approximate or not.
  // Returns either self or an approxed value.  Caller can wrap-and-return.
  private TypeFunPtr _makex( BitsFun fidxs ) {
    if( _ret==this || !(_ret instanceof TypeFunPtr tfp) )
      return this;              // Always OK.
    // Overlaps, without strictly increasing.
    if( sideways(fidxs,tfp._fidxs,tfp._ret!=XSCALAR) ) {
      Type ret = tfp._make_apx( ); // Must approx
      if( ret instanceof TypeFunPtr tfp2 && sideways(fidxs,tfp2._fidxs,tfp2._ret!=XSCALAR) )
        return add_cycle(tfp2);   // Cycle keeps rolling up
      // Wrap and return
      return make( _any, _nil, _sub, fidxs.meet(_fidxs),_nargs,_dsp,ret);
    }
    Type ret = tfp._makex(fidxs); // Continue checking to the end
    if( ret==_ret ) return this;  // No change
    return make( _any, _nil, _sub, _fidxs, _nargs, _dsp, ret);// Wrap and return
  }

  // True if the fidxs overlap and are NOT strictly increasing.
  private boolean sideways(BitsFun f0, BitsFun f1, boolean lo) {
    return f0.overlaps(f1) &&    // Overlap
      (!(f0!=f1 && f0.isa(f1)) || // NOT strictly increasing
       !lo); // or strictly increasing into hi
  }

  // MUST approx 'this'.  Recurses to the end.  Returns either SCALAR or ALL or
  // an interned-self-cycle.
  private Type _make_apx( ) {
    if( _ret==this ) return this; // Already a self-cycle
    if( _ret==XSCALAR || _ret==ANY ) // Approx self as a self-cycle
      return make_cycle( _any, _nil, _sub, _fidxs,_nargs,_dsp);
    if( !(_ret instanceof TypeFunPtr tfp) )
      return _ret==ALL ? ALL : SCALAR; // Approx self as SCALAR
    Type ret = tfp._make_apx();        // Recursive walk to the end
    if( !(ret instanceof TypeFunPtr tfp2) ) return ret; // Approx self as a SCALAR
    return add_cycle(tfp2);    // Approx self as a self-cycle merged into the returned self-cycle
  }

  // Merge into the self-cycle
  private TypeFunPtr add_cycle( TypeFunPtr cyc) {
    assert cyc._ret==cyc;
    BitsFun fidxs = _fidxs.meet(cyc._fidxs);
    int nargs = Math.min(_nargs,cyc._nargs);
    Type dsp = _dsp.meet(cyc._dsp);
    return make_cycle( _any, _nil, _sub, fidxs,nargs,dsp);
  }

  // Install a length-1 self-cycle (if 'ret' is a TFP or high) or a short
  // normal TFP if 'ret' is not a TFP.
  static TypeFunPtr make_cycle( boolean any, boolean nil, boolean sub, BitsFun fidxs, int nargs, Type dsp ) {
    TypeFunPtr tfp = malloc(any,nil,sub,fidxs,nargs,dsp,null);
    tfp._ret = tfp;             // Make a self-cycle of length 1
    assert dsp._hash!=0;        // Can be 'compute_hash'
    tfp._hash = tfp.compute_hash();
    TypeFunPtr old = (TypeFunPtr)tfp.intern_get(); // Intern check
    if( old!=null )                                // Return prior hit
      return POOLS[TFUNPTR].free(tfp,old);         // Return prior
    tfp._dual = tfp.xdual();                       // Install dual in a self-cycle
    tfp._dual._dual = tfp;
    tfp._dual._ret = tfp._dual;
    tfp._dual._hash = ~tfp._hash;
    return tfp.retern()._dual.retern().dual();     // Install self-cycle
  }

  // Allocate and init
  private static TypeFunPtr malloc(boolean any, boolean nil, boolean sub, BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(any,nil,sub,fidxs,nargs,dsp,ret);
  }
  private static TypeFunPtr malloc(BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(fidxs.above_center(),fidxs.test(0),fidxs.clear(0),nargs,dsp,ret);
  }

  public static TypeFunPtr make ( BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    boolean haz_nil = fidxs.test(0);
    boolean any = fidxs.above_center();
    boolean nil = any &&  haz_nil;
    boolean sub = any || !haz_nil;
    return _makex(any, nil, sub, fidxs.clear(0),nargs,dsp,ret,false);
  }
  public static TypeFunPtr makex( BitsFun fidxs, int nargs, Type dsp, Type ret ) {
    boolean haz_nil = fidxs.test(0);
    boolean any = fidxs.above_center();
    boolean nil = any &&  haz_nil;
    boolean sub = any || !haz_nil;
    return _makex(any, nil, sub, fidxs,nargs,dsp,ret,true );
  }
  public static TypeFunPtr make( int fidx, int nargs, Type dsp, Type ret ) { return make(BitsFun.make0(fidx),nargs,dsp,ret); }
  public static TypeFunPtr make_new_fidx( int parent, int nargs, Type dsp, Type ret ) { return make(BitsFun.make_new_fidx(parent),nargs,dsp,ret); }
  public static TypeFunPtr make( BitsFun fidxs, int nargs) { return make(fidxs,nargs,TypeMemPtr.NO_DISP,TypeNil.SCALAR); }
  public        TypeFunPtr make_from( Type dsp ) { return make(_fidxs,_nargs, dsp,_ret); }
  public        TypeFunPtr make_from( BitsFun fidxs  ) { return fidxs==_fidxs ? this : make( fidxs,_nargs,_dsp,_ret); }
  public        TypeFunPtr make_from( Type dsp, Type ret ) { return dsp==_dsp && ret==_ret ? this : make(_fidxs,_nargs, dsp,ret); }
  @Override TypeFunPtr make_from( boolean any, boolean nil, boolean sub ) {
    if( any == _any && nil == _nil && sub == _sub ) return this;
    return makex(any,nil,sub,_fidxs,_nargs,_dsp,_ret);
  }

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.NALL ,1,Type.ALL,Type.ALL);
  public  static final TypeFunPtr ARG2   =         make(BitsFun.NALL ,2,Type.ALL,Type.ALL);
  public  static final TypeFunPtr EMPTY  =         make(BitsFun.EMPTY,0,Type.ANY,Type.ANY);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,ARG2};

  @Override protected TypeFunPtr xdual() {
    boolean xor = _nil == _sub;
    return malloc(!_any,_nil^xor,_sub^xor,_fidxs.dual(),-_nargs,_dsp.dual(),_ret.dual());
  }
  @Override void rdual() { _dual._dsp = _dsp._dual;  _dual._ret = _ret._dual; }

  @Override protected TypeFunPtr xmeet( Type t ) {
    TypeFunPtr tf = (TypeFunPtr)t;
    // Meet of nilable parts
    boolean any = _any & tf._any;
    boolean nil = _nil & tf._nil;
    boolean sub = _sub & tf._sub;
    // Meet of non-return parts
    BitsFun fidxs = _fidxs.meet(tf._fidxs);
    int nargs = (_nargs ^ tf._nargs) > 0 ? Math.min(_nargs,tf._nargs) : Math.max(_nargs,tf._nargs);
    Type dsp = _dsp.meet(tf._dsp);

    // If both are short cycles, the result is a short cycle
    if( _ret==this && tf._ret==tf )
      return make_cycle(any,nil,sub,fidxs,nargs,dsp);

    // Otherwise, recursively find the return
    Type ret = _ret.meet(tf._ret);

    return makex(any,nil,sub,fidxs,nargs,dsp,ret);
  }

  public BitsFun fidxs() { return _fidxs; }
  public int fidx() { return _fidxs.getbit(); } // Asserts internally single-bit
  public int nargs() { return Math.abs(_nargs); }

  // Widens, not lowers.
  @Override public TypeFunPtr simple_ptr() {
    Type ds = _dsp.simple_ptr();
    Type rs = _ret.simple_ptr();
    if( _dsp==ds && _ret==rs ) return this;
    return make_from(ds,rs);
  }

  @Override public boolean above_center() {
    return _fidxs.above_center() || _fidxs.is_empty();
  }
  @Override public boolean is_con()       {
    // Constant display or unbound display
    return (!has_dsp() || _dsp.is_con()) &&
      // Single bit covers all functions (no new children added, but new splits
      // can appear).  Currently, not tracking this at the top-level, so instead
      // just triggering off of a simple heuristic: a single bit above BitsFun.ALL.
      _fidxs.abit() > 1 ;
  }

  @Override public Type make_from(Type head, TypeMem map, VBitSet visit) {
    throw unimpl();
  }

  // All reaching fidxs, including any function returns
  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    if( Type.ARF.tset(_uid) ) return _fidxs;
    // Myself, plus any function returns
    return _fidxs.meet(_ret._all_reaching_fidxs(tmem));
  }

}
