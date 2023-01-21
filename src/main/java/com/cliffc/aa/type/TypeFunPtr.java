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
  private BitsFun _pos;         // Known function bits

  private int _nargs;           // Number of formals, including the ctrl, mem, display
  public Type _ret;             // Return scalar type
  private Type _dsp;            // Display; often a TMP to a TS; ANY is dead (not live, nobody uses).

  private TypeFunPtr _init(BitsFun pos, int nargs, Type dsp, Type ret) {
    assert !(dsp instanceof TypeFld);
    _pos = pos;
    _nargs=nargs; _dsp=dsp; _ret=ret;
    return this;
  }
  private TypeFunPtr init(boolean any, boolean nil, BitsFun pos, int nargs, Type dsp, Type ret ) {
    super.init(any,nil);
    return _init(pos,nargs,dsp,ret);
  }
  private TypeFunPtr init(boolean any, boolean nil, boolean sub, BitsFun pos, int nargs, Type dsp, Type ret ) {
    super.init(any,nil,sub);
    return _init(pos,nargs,dsp,ret);
  }
  @Override TypeFunPtr copy() { return _copy().init(_any,_nil,_sub,_pos,_nargs,_dsp,_ret); }
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

  public static boolean has_dsp(Type dsp) { return dsp!=ANY; }
  public boolean has_dsp() { return has_dsp(_dsp); }
  public Type dsp() { return _dsp; }
  void set_dsp( Type dsp) { assert un_interned() && (has_dsp() || _dsp==dsp); _dsp = dsp; }

  // Static properties hashcode, no edge hashes
  @Override long static_hash() {
    return Util.mix_hash(super.static_hash(),_pos._hash,_nargs^_dsp._type^_ret._type);
  }

  // Static properties equals, no edges.  Already known to be the same class
  // and not-equals.
  @Override boolean static_eq(TypeFunPtr t) {
    return super.static_eq(t) && _nargs == t._nargs && _dsp._type == t._dsp._type &&
      _ret._type == t._ret._type && _pos==t._pos;
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
    if( _pos!=tf._pos || _nargs != tf._nargs ) return false;
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

  @Override public void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"X"+(char)('A'+ucnt._tfp++));
      return;
    }
    _dsp._str_dups(visit,dups,ucnt);
    _ret._str_dups(visit,dups,ucnt);
  }


  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _any ) sb.p('~');
    _pos.str(sb);
    sb.p('{');                  // Arg list start
    if( debug ) _dsp._str(visit,dups, sb, true, indent).p(",");
    sb.p(_nargs).p(" ->");
    boolean ind = indent && _ret._str_complex(visit,dups);
    if( ind ) sb.nl().ii(1).i();
    else sb.p(' ');
    _ret._str(visit,dups, sb, debug, indent).p(' ');
    if( ind ) sb.nl().di(1).i();
    return _str_nil(sb.p('}'));
  }

  @Override boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) {
    return this!=_ret && _ret._str_complex(visit,dups);
  }

  static TypeFunPtr valueOf(Parse P, String cid, boolean any) {
    BitsFun pos = P.bits(BitsFun.EMPTY);
    if( P.peek('+') ) throw unimpl();
    P.require('{');
    TypeFunPtr tfp = malloc(any,pos,0,null,null);
    if( cid!=null ) P._dups.put(cid,tfp);
    tfp.set_dsp(P.type());
    P.require(',');
    tfp._nargs = (int)P._num();
    P.require('-');  P.require('>');
    tfp._ret = P.type();
    P.require('}');
    return tfp.val_nil(P);
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
      for( int fidx : tfp.pos() ) if( CHK2.tset(fidx) ) return false;
      if( !(tfp._ret instanceof TypeFunPtr ret) ) break;
      if( tfp._pos.is_empty() && ret._pos.is_empty() ) return false;
      tfp = ret;
    }
    return true;
  }

  // Functions can grow indefinitely, if being built in a recursive loop.
  // We check that fidx return invariant holds.
  public static TypeFunPtr make( boolean any, boolean nil, boolean sub, BitsFun pos, int nargs, Type dsp, Type ret ) {
    TypeFunPtr tfp = malloc(any, nil, sub, pos, nargs,dsp,ret).hashcons_free();
    assert check2(tfp);          // Assert new return-chain is valid
    return tfp;
  }

  // Assert the ret has the invariant.
  // Make the TFP, which might not have the invariant.
  // Call _rule2; the result has the invariant.
  // Check and return.
  public static TypeFunPtr makex( boolean any, boolean nil, boolean sub, BitsFun pos, int nargs, Type dsp, Type ret ) {
    assert !(ret instanceof TypeFunPtr rtfp) || check2(rtfp); // Assert old return-chain is valid
    // Make the TFP, but it may NOT pass the invariant
    TypeFunPtr tfp = malloc(any, nil, sub, pos, nargs,dsp,ret).hashcons_free();
    CHK2.clear();
    TypeFunPtr tfp2 = tfp._rule2(pos,true); // Approx
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
  private TypeFunPtr _rule2(BitsFun new_pos, boolean first) {
    if( this==_ret ) return this; // Self-cycle, end is fine
    if( !first && new_pos.overlaps(_pos) )
      return _rule2_apx(); // Overlaps, so do hard approximation

    if( !(_ret instanceof TypeFunPtr rtfp) || rtfp==this )
      return this;              // End is fine, either self-cycle or a non-TFP

    TypeFunPtr tfp = rtfp._rule2(new_pos,false);
    if( tfp==_ret ) return this; // Return was fine, so i am fine
    if( tfp==null ) return make_from(_dsp,rtfp._ret); // Hard fail
    if( new_pos.overlaps(tfp._pos) ) {
      if( new_pos.is_empty() && tfp._pos.is_empty() )
        return tfp;             // Avoid 2 empties in a row
      return make_from(_dsp,tfp._ret);
    }
    return make_from(_dsp,tfp);  // Wrap the return
  }

  private TypeFunPtr _rule2_apx() {
    if( this==_ret ) return this; // I am my own self-cycle
    if( !(_ret instanceof TypeFunPtr rtfp) ) { // Ret is not a TFP?
      if( _ret.isa(GENERIC_FUNPTR) )           // _ret is very high and falls to a cycle?
        return make_cycle(_any,_nil,_sub,_pos,_nargs,_dsp);
      return null;              // Hard fail, return low self; parent will wrap this low return
    }
    TypeFunPtr apx = rtfp._rule2_apx();
    if( apx==null ) return make_from(_dsp,rtfp._ret);
    // Fold my _fidxs into return cycle and return
    return make_cycle(_any,_nil,_sub,_pos.meet(apx._pos),_nargs,_dsp);
  }

  // Install a length-1 self-cycle
  static TypeFunPtr make_cycle( boolean any, boolean nil, boolean sub, BitsFun pos, int nargs, Type dsp ) {
    TypeFunPtr tfp = malloc(any,nil,sub,pos,nargs,dsp,null);
    tfp._ret = tfp;             // Make a self-cycle of length 1
    assert dsp._hash!=0;        // Can be 'compute_hash'
    tfp._cyc_hash = tfp.static_hash(); // Cycle hash is the XOR of all static hashes
    tfp._hash = tfp.compute_hash();
    TypeFunPtr old = (TypeFunPtr)tfp.intern_get(); // Intern check
    if( old!=null )                                // Return prior hit
      return POOLS[TFUNPTR].free(tfp,old);         // Return prior
    TypeFunPtr tfpd = tfp._dual = tfp.xdual(); // Install dual in a self-cycle
    tfpd._dual = tfp;
    tfpd._ret = tfpd;
    tfpd._cyc_hash = tfpd.static_hash(); // Cycle hash is the XOR of all static hashes
    tfpd._hash = tfpd.compute_hash();
    return tfp.retern()._dual.retern().dual(); // Install self-cycle
  }

  // Allocate and init
  private static TypeFunPtr malloc(boolean any, boolean nil, boolean sub, BitsFun pos, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(any,nil,sub,pos,nargs,dsp,ret);
  }
  private static TypeFunPtr malloc(boolean any, BitsFun pos, int nargs, Type dsp, Type ret ) {
    TypeFunPtr t1 = POOLS[TFUNPTR].malloc();
    return t1.init(any,pos.test(0),pos.clear(0),nargs,dsp,ret);
  }

  public static TypeFunPtr make( boolean any, BitsFun pos, int nargs, Type dsp, Type ret ) {
    boolean haz_nil = pos.test(0);
    boolean nil = any &&  haz_nil;
    boolean sub = any || !haz_nil;
    return make(any, nil, sub, pos, nargs,dsp,ret);
  }
  public static TypeFunPtr makex( boolean any, BitsFun pos, int nargs, Type dsp, Type ret ) {
    boolean haz_nil = pos.test(0);
    boolean nil = any &&  haz_nil;
    boolean sub = any || !haz_nil;
    return makex(any, nil, sub, pos.clear(0), nargs,dsp,ret);
  }
  public static TypeFunPtr make( int fidx, int nargs, Type dsp, Type ret ) {
    return make(false,BitsFun.make0(fidx),nargs,dsp,ret);
  }
  public static TypeFunPtr make_new_fidx( int parent, int nargs, Type dsp, Type ret ) {
    return make(BitsFun.new_fidx(parent),nargs,dsp,ret);
  }
  public static TypeFunPtr make( BitsFun pos, int nargs) {
    return make(pos.above_center(),pos,nargs,TypeMemPtr.NO_DISP,TypeNil.SCALAR);
  }
  public TypeFunPtr make_from( Type dsp ) { return make(_any, _pos,_nargs, dsp,_ret); }
  public TypeFunPtr make_from( BitsFun pos ) {
    return pos==_pos ? this : malloc( pos.above_center(), _nil, _sub, pos, _nargs,_dsp,_ret).hashcons_free();
  }

  public TypeFunPtr make_from( Type dsp, Type ret ) { return dsp==_dsp && ret==_ret ? this : make(_any, _pos,_nargs, dsp,ret); }
  @Override TypeFunPtr make_from( boolean nil, boolean sub ) { return makex(_any,nil,sub,_pos,_nargs,_dsp,_ret); }

  public  static final TypeFunPtr GENERIC_FUNPTR = make(false,BitsFun.NALL ,1,Type.ALL,Type.ALL);
  public  static final TypeFunPtr GENERIC_FUNPTR0= make(false,BitsFun.NALL.set(0),1,Type.ALL,Type.ALL);
  public  static final TypeFunPtr ARG2   =         make(false,BitsFun.NALL ,2,Type.ALL,Type.ALL);
  public  static final TypeFunPtr THUNK  =         make(false,false,false,BitsFun.NALL ,3,Type.ALL,Type.ALL); // zero-arg function (plus ctrl, mem, display)
  public  static final TypeFunPtr EMPTY  =         make(false,BitsFun.EMPTY,1,Type.ANY,Type.ANY);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR,ARG2,THUNK};

  @Override protected TypeFunPtr xdual() {
    boolean xor = _nil == _sub;
    return malloc(!_any,_nil^xor,_sub^xor,_pos.dual(),-_nargs,_dsp.dual(),_ret.dual());
  }
  @Override void rdual() { _dual._dsp = _dsp._dual;  _dual._ret = _ret._dual; }

  @Override protected TypeFunPtr xmeet( Type t ) {
    TypeFunPtr tf = (TypeFunPtr)t;
    // Meet of nilable parts
    boolean any = _any & tf._any;
    boolean nil = _nil & tf._nil;
    boolean sub = _sub & tf._sub;
    // Meet of non-return parts
    BitsFun pos = _pos.meet(tf._pos);
    int nargs = (_nargs ^ tf._nargs) > 0 ? Math.min(_nargs,tf._nargs) : Math.max(_nargs,tf._nargs);
    Type dsp = _dsp.meet(tf._dsp);

    // If both are short cycles, the result is a short cycle
    if( _ret==this && tf._ret==tf )
      return make_cycle(any,nil,sub,pos,nargs,dsp);

    // Otherwise, recursively find the return
    Type ret = _ret.meet(tf._ret);

    return makex(any,nil,sub,pos,nargs,dsp,ret);
  }

  // All fidxs, whether meet or join
  public BitsFun fidxs() { return _pos; }
  public BitsFun pos() { return _pos; }
  public int fidx() { return _pos.getbit(); } // Asserts internally single-bit
  public boolean is_fidx() { return _pos.abit()>-1; } // Single-bit TFP
  public boolean test(int fidx) { return _pos.test_recur(fidx); }
  public boolean is_empty() { return _pos.is_empty(); }
  public boolean is_full() { return _pos==BitsFun.NALL; }
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
