package com.cliffc.aa.type;

import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;

import static com.cliffc.aa.AA.unimpl;

public class TypeNil<N extends TypeNil<N>> extends Type<N> {
  public boolean _any;  // any vs all
  // OR  =   nil &  sub // NIL choice and subclass choice
  // YES =   nil & !sub // YES nil and ignore/no subclass
  // NO  =  !nil &  sub // NO nil and use the subclass
  // AND =  !nil & !sub // no-nil-choice and no-subclass-choice so must have both nil and subclass

  public boolean _nil; // true for OR-NIL and YES-NIL.  False for AND-NIL, NOT-NIL
  public boolean _sub; // true for OR-NIL and NOT-NIL.  False for AND-NIL, YES-NIL

  N init( boolean any, boolean nil, boolean sub ) {
    super.init();
    _any = any;
    _nil = nil;
    _sub = sub;
    return (N)this;
  }
  // Convenience for many subclasses.  Supports only half the total choices
  // any &&  haz_nil == ~scalar OR  NIL ; XSCALAR;  nil &  sub
  // any && !haz_nil == ~scalar NOT NIL ; XNSCALR; !nil &  sub
  // all &&  haz_nil ==  scalar AND NIL ;  SCALAR; !nil & !sub
  // all && !haz_nil ==  scalar NOT NIL ;  NSCALR; !nil &  sub
  void init( boolean any, boolean haz_nil) {
    super.init();
    _any = any;
    _nil = any &&  haz_nil;
    _sub = any || !haz_nil;
  }

  @Override protected N _copy() {
    N n = super._copy();
    n._any = _any;
    n._nil = _nil;
    n._sub = _sub;
    return n;
  }

  @Override long static_hash() { return
      super.static_hash() ^
      (_any ? (1L<<16):1) |
      (_sub ? (1L<<19):1) |
      (_nil ? (1L<<21):1) ;
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeNil tn) || _type != tn._type ) return false;
    return _any==tn._any && _sub ==tn._sub && _nil ==tn._nil;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  // Static properties equals; edges are IGNORED.  Already known to be the same
  // class and not-equals.
  boolean static_eq(N t) {
    if( this==t ) return true;
    if( _type != t._type ) return false;
    return _any==t._any && _sub ==t._sub && _nil ==t._nil;
  }

  static final String[][][] NSTRS = new String[][][]{
    {{ ""    , "n"},  // all, !nil, {!sub,sub}  AND, NOT
     { "nil=","0+"}}, // all,  nil, {!sub,sub}  YES, OR
    {{ "0&~" ,"~n"},  // any, !nil, {!sub,sub}  AND, NOT
     {"xnil~","~" }}  // any,  nil, {!sub,sub}  YES, OR
  };
  SB _strn(SB sb) { return sb.p(NSTRS[_any ?1:0][_nil ?1:0][_sub ?1:0]); }
  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    assert this.getClass().equals(TypeNil.class);  // Subclasses handle directly
    if( this== NIL ) return sb.p( "nil");
    if( this==XNIL ) return sb.p("xnil");
    return _strn(sb).p("Scalar");
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
    if( P.peek("=0") ) throw unimpl();
    return (N)this;
  }
  
  static {
    new Pool( TNIL, new TypeNil());
  }
  static TypeNil make( boolean any, boolean nil, boolean sub ) {
    TypeNil tn = POOLS[TNIL].malloc();
    return (TypeNil)tn.init(any, nil, sub).hashcons_free();
  }
  TypeNil make_from( boolean any, boolean nil, boolean sub ) { throw unimpl(); }

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
  public static final TypeNil  NIL = make(false,true,false); // One of many nil choices
  public static final TypeNil XNIL = make(true ,true,false); // One of many nil choices
  public static final TypeNil AND_XSCALAR = make(true,false,false); // Odd choice: 0&~Scalar
  // Collection of sample types for checking type lattice properties.
  static final TypeNil[] TYPES = new TypeNil[]{SCALAR,NSCALR,NIL};
  static Type valueOfNil(String cid) {
    return switch(cid) {
    case  "Scalar" ->  SCALAR;
    case "nScalar" -> NSCALR;
    case "xnil"    -> XNIL;
    case "nil"     -> NIL;
    default        -> null;
    };
  }

  // duals:
  //  xs +0 <->  s &0
  //  xs &0 <->  s +0
  //  xs =0 <->  s =0 // oddly YES-nil stays YES-nil
  //  xs!=0 <->  s!=0 // and   NOT-nil stays NOT-nil
  @Override protected N xdual() {
    boolean xor = _nil == _sub;
    return POOLS[_type].<N>malloc().init(!_any, _nil^xor, _sub^xor);
  }

  // Only called TNIL to TNIL
  @Override protected TypeNil xmeet(Type t) {
    assert _type==TNIL && t._type==TNIL && this!=t;
    TypeNil tn = (TypeNil)t;
    boolean any = _any & tn._any;
    boolean nil = _nil & tn._nil;
    boolean sub = _sub & tn._sub;
    // No edge to nil
    TypeNil rez = make(any,nil,sub);
    if( rez==NIL && (tn==XNIL || this==XNIL) )
      return SCALAR;
    return rez;
  }

  // LHS is TypeNil directly; RHS is a TypeNil subclass
  final TypeNil nmeet(TypeNil tn) {
    assert _type==TNIL && tn._type!=TNIL;
    boolean any = _any & tn._any;
    boolean nil = _nil & tn._nil;
    boolean sub = _sub & tn._sub;
    if( !_any ) return make(any,nil,sub); // Falling past 'tn' to a low TypeNil
    // If type would fall to subtype YES-nil, fall to AND-nil instead
    nil &= sub;
    return tn.make_from(any,nil,sub);
  }

  // Meet the nil bits, but the subclass parts are not the same.
  // Fall to a TypeNil.
  TypeNil cross_nil( TypeNil tn ) {
    assert _type!=tn._type && _type!=TNIL && tn._type!=TNIL;   // Unrelated subclass parts
    boolean any = false; // Unrelated sub-parts cannot keep their choices; falls to Scalar-plus-nil-whatever
    boolean nil = _nil & tn._nil;
    boolean sub = _sub & tn._sub;
    int idxn = nil ? 1 : 0;
    int idxs = sub ? 1 : 0;
    TypeInt    int0= TypeInt   .MINMAX[idxn][idxs]; //.make(false,nil,sub,1,0);
    TypeFlt    flt = TypeFlt   .MINMAX[idxn][idxs]; //.make(false,nil,sub,32,0);
    TypeMemPtr tmp = TypeMemPtr.MINMAX[idxn][idxs]; //.EMTPTR.make_from(false,nil,sub);
    TypeFunPtr tfp = TypeFunPtr.MINMAX[idxn][idxs]; //.make(BitsFun.EMPTY,999,Type.ANY,Type.ANY).make_from(false,nil,sub);
    switch( this ) {
    case TypeInt    tint: { int0=(TypeInt   )int0.meet(tint); break; }
    case TypeFlt    tflt: { flt =(TypeFlt   )flt .meet(tflt); break; }
    case TypeMemPtr ttmp: { tmp =(TypeMemPtr)tmp .meet(ttmp); break; }
    case TypeFunPtr ttfp: { tfp =(TypeFunPtr)tfp .meet(ttfp); break; }
    case TypeRPC    trpc: return make(any,nil,sub);
    default: throw unimpl();
    }
    switch( tn ) {
    case TypeInt    tint: { int0=(TypeInt   )int0.meet(tint); break; }
    case TypeFlt    tflt: { flt =(TypeFlt   )flt .meet(tflt); break; }
    case TypeMemPtr ttmp: { tmp =(TypeMemPtr)tmp .meet(ttmp); break; }
    case TypeFunPtr ttfp: { tfp =(TypeFunPtr)tfp .meet(ttfp); break; }
    case TypeRPC    trpc: return make(any,nil,sub);
    default: throw unimpl();
    }
    return TypeUnion.make(any,nil,sub,int0,flt,tmp,tfp);
  }
  TypeNil as_nil() { return make(false,_nil,_sub); }

  // Type must support a nil
  public boolean must_nil() { return !_sub; }

  @Override public boolean above_center() { return _any; }

  @Override public boolean is_con() { return this==XNIL || this==NIL; }

  @Override public Type widen() { return this; }

  // Parser init
  public static void init0( HashMap<String,Type> types ) {
    types.put("scalar",SCALAR);
    TypeInt.init1(types);
    TypeFlt.init1(types);
    TypeStruct.init1();
  }
}
