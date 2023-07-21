package com.cliffc.aa.type;

import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;

public class TypeNil<N extends TypeNil<N>> extends Type<N> {
  public boolean _any;  // any vs all
  // OR  =   nil &  sub // NIL choice and subclass choice
  // YES =   nil & !sub // YES nil and ignore/no subclass
  // NO  =  !nil &  sub // NO nil and use the subclass
  // AND =  !nil & !sub // no-nil-choice and no-subclass-choice so must have both nil and subclass

  public boolean _nil; // true for OR-NIL and YES-NIL.  False for AND-NIL, NOT-NIL
  public boolean _sub; // true for OR-NIL and NOT-NIL.  False for AND-NIL, YES-NIL

  // Track precision of aliases and fidxs for type unions; mostly means
  // externally passed-in parameters have limits on which aliases they can
  // pass-in (escaped aliases yes, but internal and not escaped, no).

  // List of known memory aliases.  Zero is nil.
  public BitsAlias _aliases;

  // List of known functions in set, or 'flip' for choice-of-functions.
  // A single bit is a classic code pointer.
  public BitsFun   _fidxs;

  N init( boolean any, boolean nil, boolean sub ) {
    return init(any,nil,sub,balias(any),bfun(any));
  }

  N init( boolean any, boolean nil, boolean sub, BitsAlias aliases, BitsFun fidxs ) {
    assert !aliases.test(0) && !fidxs.test(0); // Nil uses the nil boolean
    super.init();
    _any = any;
    _nil = nil;
    _sub = sub;
    _aliases = aliases;
    _fidxs = fidxs;
    return (N)this;
  }

  N chk() {
    // Invariant: above/below match on aliases, except for EMPTY (so we both a hi and lo empty)
    //assert _aliases.above_center()==_any || _aliases==BitsAlias.EMPTY ;
    return (N)this;
  }

  static BitsAlias balias(boolean any) { return any ? BitsAlias.NANY : BitsAlias.NALL; }
  static BitsFun   bfun  (boolean any) { return any ? BitsFun  .NANY : BitsFun  .NALL; }

  @Override N copy() {
    N n = super.copy();
    n._any = _any;
    n._nil = _nil;
    n._sub = _sub;
    n._aliases = _aliases;
    n._fidxs = _fidxs;
    return n;
  }

  @Override long static_hash() {
    return super.static_hash() ^
      ((_any ? (1L<<16):1) |
       (_sub ? (1L<<19):1) |
       (_nil ? (1L<<21):1)) ^
      _aliases._hash ^
      _fidxs  ._hash ;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeNil tn) || _type != tn._type ) return false;
    return _eq(tn);
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  // Static properties equals; edges are IGNORED.  Already known to be the same
  // class and not-equals.
  boolean static_eq(N t) {
    if( this==t ) return true;
    if( _type != t._type ) return false;
    return _eq(t);
  }
  boolean _eq(TypeNil tn) {
    return _any==tn._any && _nil==tn._nil && _sub==tn._sub &&
      _aliases==tn._aliases && _fidxs==tn._fidxs;
  }

  static final String[][][] NSTRS = new String[][][]{
    {{ ""    , "n" },  // all, !nil, {!sub,sub}  AND, NOT
     { "nil_","_0" }}, // all,  nil, {!sub,sub}  YES, OR
    {{ "~_0" ,"~n" },  // any, !nil, {!sub,sub}  AND, NOT
     {"~nil_","~"  }}  // any,  nil, {!sub,sub}  YES, OR
  };
  SB _strn(SB sb) { return sb.p(NSTRS[_any ?1:0][_nil ?1:0][_sub ?1:0]); }
  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    assert this.getClass().equals(TypeNil.class);  // Subclasses handle directly
    if( this== NIL ) return sb.p( "nil");
    if( this==XNIL ) return sb.p("xnil");
    if(  _any && _aliases==BitsAlias.NANY && _fidxs==BitsFun.NANY )
      return _strn(sb).p("Scalar");
    if( !_any && _aliases==BitsAlias.NALL && _fidxs==BitsFun.NALL )
      return _strn(sb).p("Scalar");
    // Fancy with aliases and fidxs
    if( _any ) sb.p('~');
    _aliases.str(sb.p('%'));
    _fidxs  .str(sb);
    return _str_nil(sb);
  }
  // Called from subclasses, which already handle _any.  Appends something for may/must.
  private static final String[][] XSTRS = new String[][]{
    { "?" , ""  }, // all, !nil, {!sub,sub}
    { "=0", "+0"}  // all,  nil, {!sub,sub}
  };
  SB _str_nil( SB sb ) { return sb.p(XSTRS[_nil ?1:0][_sub ?1:0]); }

  N val_nil( Parse P ) {
    if( P.peek('?' ) ) _nil = _sub = false;
    if( P.peek("+0") ) _nil = _sub = true;
    if( P.peek("=0") ) { _nil=true; _sub=false; }
    return (N)this;
  }

  static Type valueOfNil(String cid) {
    return switch(cid) {
    case  "Scalar" ->   SCALAR; // FFF
    case "nScalar" ->  NSCALR ; // FFT
    case "nil"     ->  NIL;     // FTF
    case "xnil"    -> XNIL;     // TTF
    case "_0Scalar" -> make(false,true,true);
    default        -> null;
    };
  }

  static TypeNil valueOf(Parse P, String cid, boolean any) {
    P.require('%');
    var aliases = P.bits(BitsAlias.EMPTY);
    var fidxs   = P.bits(BitsFun  .EMPTY);
    TypeNil tn = (TypeNil)malloc(any,false,true,aliases,fidxs).val_nil(P).chk().hashcons_free();
    if( cid!=null ) P._dups.put(cid,tn);
    return tn;
  }

  static {
    new Pool( TNIL, new TypeNil());
  }
  public static TypeNil malloc( boolean any, boolean nil, boolean sub, BitsAlias aliases, BitsFun fidxs ) {
    TypeNil tn = POOLS[TNIL].malloc();
    return tn.init(any, nil, sub, aliases, fidxs);
  }
  public static TypeNil make( boolean any, boolean nil, boolean sub, BitsAlias aliases, BitsFun fidxs ) {
    return (TypeNil)malloc(any, nil, sub, aliases, fidxs).chk().hashcons_free();
  }
  static TypeNil make( boolean any, boolean nil, boolean sub ) {
    TypeNil tn = POOLS[TNIL].malloc();
    return (TypeNil)tn.init(any, nil, sub).chk().hashcons_free();
  }

  // Plain TypeNil (no subclass) has 8 possibilities:
  // XSCALAR OR  NIL  -- choice of anything
  // XSCALAR NO  NIL  -- similar XNSCALR
  // XSCALAR YES NIL  -- NIL, drop XSCALAR
  // XSCALAR AND NIL  -- must allow nil, but then choice of anything
  //  SCALAR OR  NIL  -- weird: choice of NIL or must be Scalar
  //  SCALAR NO  NIL  -- similar NSCALR
  //  SCALAR YES NIL  -- NIL, drop SCALAR
  //  SCALAR AND NIL  -- must support everything
  public static final TypeNil  SCALAR= make(false,false,false); // ptrs, ints, flts, nil; things that fit in a machine register
  public static final TypeNil  NSCALR= make(false,false,true ); // ptrs, ints, flts     ; things that fit in a machine register
  public static final TypeNil XSCALAR= (TypeNil)SCALAR.dual();
  public static final TypeNil XNSCALR= (TypeNil)NSCALR.dual();
  public static final TypeNil XNIL = make(false,true,false); // One of many nil choices
  public static final TypeNil  NIL = make(true ,true,false); // One of many nil choices
  public static final TypeNil AND_XSCALAR = make(true,false,false); // Odd choice: 0&~Scalar

  public static final TypeNil INTERNAL = make(false,false,false,BitsAlias.LOC,BitsFun.INT);
  public static final TypeNil EXTERNAL = make(false,false,false,BitsAlias.EXT,BitsFun.EXT);
  public static final TypeNil TEST0 = make(false,true,false,BitsAlias.EXT,BitsFun.INT);
  public static final TypeNil NO_DSP = XSCALAR;
  // Collection of sample types for checking type lattice properties.
  static final TypeNil[] TYPES = new TypeNil[]{SCALAR,NSCALR,XNIL,(TypeNil)AND_XSCALAR._dual,INTERNAL,TEST0};

  // duals:
  //  xs +0 <->  s &0
  //  xs &0 <->  s +0
  //  xs =0 <->  s =0 // oddly YES-nil stays YES-nil
  //  xs!=0 <->  s!=0 // and   NOT-nil stays NOT-nil
  @Override protected N xdual() {
    boolean xor = _nil == _sub;
    return POOLS[_type].<N>malloc().init(!_any, _nil^xor, _sub^xor, _aliases.dual(), _fidxs.dual());
  }

  // Only called TNIL to TNIL
  @Override protected TypeNil xmeet(Type t) {
    assert _type==TNIL && t._type==TNIL && this!=t;
    N tn = (N)t;              // Invariant from caller
    TypeNil rez = ymeet(tn);  // Invariant from caller
    // No edge xnil -> nil.  See testLattice22_nil2()
    if( rez.nil_ish() &&
        (tn.xnil_ish() || xnil_ish()) )
       rez._nil=false;
    return (TypeNil)rez.chk().hashcons_free();
  }
  final boolean xnil_ish() { return  _any && yes_ish(); }
  final boolean  nil_ish() { return !_any && yes_ish(); }
  final boolean  yes_ish() { return  _nil && !_sub;  }
  final boolean   or_ish() { return  _nil &&  _sub; }


  // Meet into a new TypeNil subclass, without interning
  final N ymeet( N tn ) {
    N rez = copy();
    rez._any = _any & tn._any;
    rez._nil = _nil & tn._nil;
    rez._sub = _sub & tn._sub;
    rez._aliases = _aliases.meet(tn._aliases);
    rez._fidxs   = _fidxs  .meet(tn._fidxs  );
    return rez;
  }

  final TypeNil nmeet(TypeNil tsub) {
    assert _type==TNIL && tsub._type!=TNIL;
    if( !_any || !tsub.chk(_aliases) ) {
      TypeNil tn = tsub.widen_sub();
      return tn==this ? this : xmeet(tn);
    }
    // Keep subclass structure.  
    TypeNil rez = tsub.ymeet(this);
    rez._nil &= _sub & tsub._sub; // Disallow the xnil->nil edge
    return (TypeNil)rez.canonicalize().chk().hashcons_free();
  }
  
  // is allowed to be int or flt
  boolean chk(BitsAlias aliases) { return true; }

  N canonicalize() { return (N)this; }

  // Widen subtype to a TypeNil, losing its sub structure.
  TypeNil widen_sub() { assert _type!= TNIL; return make(false,_nil,_sub,_aliases,_fidxs); }

  // Type must support a nil
  @Override public boolean must_nil() { return !_sub; }

  @Override public boolean above_center() { return _any; }

  @Override public boolean is_con() { return above_center(); }

  @Override public Type widen() { return this; }

  @Override public long getl() {
    return this==NIL ? 0 : super.getl();
  }

  // Parser init
  public static void init0( HashMap<String,TypeNil> types ) {
    types.put("scalar",SCALAR);
    TypeInt.init1(types);
    TypeFlt.init1(types);
    TypeMemPtr.init1(types);
    TypeStruct.init1();
  }
}
