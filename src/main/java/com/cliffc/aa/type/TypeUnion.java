package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.function.*;

import static com.cliffc.aa.AA.*;

// Internal fixed-length non-recursive union of other types.  Used to represent
// either an overload (_any is true, type is high, all choices allowed), or an
// error (_any is false, conflicting types present).

// After much trial and error, I believe that all the internal members, and the
// external union must have the same setting for the _nil and _any flags, or
// else we lose associativity or symmetry.

// Since contains a TMP (and TFP), must implement Cyclic are participates in
// cyclic type construction.
public class TypeUnion extends TypeNil<TypeUnion> implements Cyclic {
  private TypeInt    _int;
  public  TypeFlt    _flt;
  private TypeMemPtr _tmp;
  private TypeFunPtr _tfp;
  
  protected TypeUnion init( boolean any, boolean nil, boolean sub, TypeInt int0, TypeFlt flt, TypeMemPtr tmp, TypeFunPtr tfp ) {
    super.init(any,nil,sub);
    _int = int0;
    _flt = flt;
    _tmp = tmp;
    _tfp = tfp;
    assert (any==int0._any || int0.is_con()) && (any==flt._any || flt.is_con()) && (tmp==null || (any==tmp._any && any==tfp._any));
    assert  nil==int0._nil                   &&  nil==flt._nil                  && (tmp==null || (nil==tmp._nil && nil==tfp._nil));
    return this;
  }

  @Override public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) { return reduce.apply(map.map(_tmp,"tmp"), map.map(_tfp,"tfp")); }
  @Override public long lwalk( LongStringFunc map, LongOp reduce ) { return reduce.run(map.run(_tmp,"tmp"), map.run(_tfp,"tfp")); }
  @Override public void walk( TypeStrRun map ) { map.run(_tmp,"tmp"); map.run(_tfp,"tfp"); }
  @Override public void walk_update( TypeMap map ) { _tmp = (TypeMemPtr)map.map(_tmp); _tfp = (TypeFunPtr)map.map(_tfp); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    TypeUnion tu = (TypeUnion)t;
    Cyclic.Link mlk = Cyclic._path_diff(_tmp,tu._tmp,links);
    Cyclic.Link flk = Cyclic._path_diff(_tfp,tu._tfp,links);
    return Cyclic.Link.min(mlk,flk); // Min depth
  }
  
  @Override public long static_hash( ) {
    return Util.mix_hash(super.static_hash(),_int._hash,_flt._hash,_tmp._aliases._hash,_tfp.fidxs()._hash);
  }
  // Static properties equals.  Already known to be the same class and
  // not-equals.  Ignore edges.
  @Override boolean static_eq(TypeUnion t) {
    return super.static_eq(t) && _int==t._int && _flt==t._flt && _tmp.static_eq(t._tmp) && _tfp.static_eq(t._tfp);
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeUnion t) ) return false;
    return _hash == t._hash && super.equals(t) && 
      _int==t._int &&
      _flt==t._flt &&
      _tmp==t._tmp &&
      _tfp==t._tfp;
  }
  // Never part of a cycle so the normal equals works
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeUnion tu) ) return false;
    if( !super.equals(tu) ) return false;
    if( _int != tu._int || _flt != tu._flt ) return false;
    if( _tmp == tu._tmp && _tfp == tu._tfp ) return true;
    return _tmp.cycle_equals(tu._tmp) && _tfp.cycle_equals(tu._tfp);
  }

  @Override void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    _int._str_dups(visit,dups,ucnt);
    _flt._str_dups(visit,dups,ucnt);
    _tmp._str_dups(visit,dups,ucnt);
    _tfp._str_dups(visit,dups,ucnt);
  }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    sb.p(_any?"~":" ");    
    sb.p("&[");
    _int._str(visit,dups, sb, debug, indent );
    sb.p(_any?" + ":" & ");
    _flt._str(visit,dups, sb, debug, indent );
    sb.p(_any?" + ":" & ");
    _tmp._str(visit,dups, sb, debug, indent );
    sb.p(_any?" + ":" & ");
    _tfp._str(visit,dups, sb, debug, indent );
    return _str_nil(sb.p(" ]"));
  }
  
  static TypeUnion valueOf(Parse P, String cid, boolean any) {
    P.require('&');
    P.require('[');
    TypeInt int0= (TypeInt   )P.type();   P.require(any ? '+' : '&');
    TypeFlt flt = (TypeFlt   )P.type();   P.require(any ? '+' : '&');
    TypeUnion  tu  = malloc(any,int0._nil,int0._sub,int0,flt,null,null);
    if( cid!=null ) P._dups.put(cid,tu);
    tu._tmp = (TypeMemPtr)P.type();   P.require(any ? '+' : '&');
    tu._tfp = (TypeFunPtr)P.type();
    P.require(']');
    if( P.peek('?') )
      tu = (TypeUnion)tu.meet(TypeNil.XNIL);
    return tu;
  }

  static { new Pool(TUNION,new TypeUnion()); }
  private static TypeUnion malloc( boolean any, boolean nil, boolean sub, TypeInt int0, TypeFlt flt, TypeMemPtr tmp, TypeFunPtr tfp ) {
    TypeUnion t1 = POOLS[TUNION].malloc();
    return t1.init(any,nil,sub,int0,flt,tmp,tfp);
  }

  public static TypeUnion make( boolean any, boolean nil, boolean sub, TypeInt int0, TypeFlt flt, TypeMemPtr tmp, TypeFunPtr tfp ) { return malloc(any,nil,sub,int0,flt,tmp,tfp).hashcons_free(); }
  // AND bits into all children
  TypeUnion make_from(boolean any, boolean nil, boolean sub ) {
    any &= _any;
    nil &= _nil;
    sub &= _sub;
    // If type would fall to subtype YES-nil, fall to AND-nil instead.
    nil &= sub; 
    TypeInt    int0= _int.make_from( any, nil, sub );
    TypeFlt    flt = _flt.make_from( any, nil, sub );
    TypeMemPtr tmp = _tmp.make_from( any, nil, sub );
    TypeFunPtr tfp = _tfp.make_from( any, nil, sub );
    return make(any, nil, sub, int0, flt, tmp, tfp);
  }

  public TypeInt    _int() { return _int; }
  public TypeFlt    _flt() { return _flt; }
  public TypeMemPtr _tmp() { return _tmp; }
  public TypeFunPtr _tfp() { return _tfp; }
  
  public static final TypeUnion TEST1 = make(true ,false,true ,TypeInt.NINT64.dual(),TypeFlt.PI   ,TypeMemPtr.ISUSED.dual(),TypeFunPtr.GENERIC_FUNPTR.dual());
  public static final TypeUnion TEST2 = make(false,false,false,TypeInt.INT8         ,TypeFlt.FLT64,TypeMemPtr.ISUSED0      ,TypeFunPtr.THUNK                );
  static final TypeUnion[] TYPES = new TypeUnion[]{/*TEST1.dual(),*/TEST2};

  // The length of Tuples is a constant, and so is its own dual.  Otherwise,
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeUnion xdual() {
    boolean xor = _nil == _sub;
    return malloc(!_any,_nil^xor,_sub^xor, _int.dual(), _flt.dual(), _tmp.dual(), _tfp.dual());
  }
  void rdual() { throw unimpl(); }

  // Meet 2 Unions together
  @Override protected TypeNil xmeet( Type t ) {
    TypeUnion tu = (TypeUnion)t;
    boolean any = _any & tu._any;
    boolean nil = _nil & tu._nil;
    boolean sub = _sub & tu._sub;
    if( !this._any ) { sub &= tu  .and_sub(); }
    if( !tu  ._any ) { sub &= this.and_sub(); }    
    return make(any,nil,sub,
                (TypeInt   )_int.meet(tu._int),
                (TypeFlt   )_flt.meet(tu._flt),
                (TypeMemPtr)_tmp.meet(tu._tmp),
                (TypeFunPtr)_tfp.meet(tu._tfp) );
  }

  // Meet a Union and a primitive.  TypeUnion sits between TypeNil and the
  // nil-able subclasses.  All primitives derive from TypeNil, and the Unions
  // Nil-ness is either all above or all below the primitives.
  // ~Scalar -> ~Union -> ~int -> ... -> int -> Union -> Scalar.
  Type umeet( TypeNil tn ) {
    if( _any ) {
      // High union, subclasses fall "out of" the Union
      return switch (tn) {
        case TypeInt    tint -> tint.meet(_int);
        case TypeFlt    tflt -> tflt.meet(_flt);
        case TypeMemPtr ttmp -> ttmp.meet(_tmp);
        case TypeFunPtr ttfp -> ttfp.meet(_tfp);
        case TypeRPC    trpc -> TypeNil.make(false,_nil&tn._nil,_sub&tn._sub);
        case TypeNil    ttn  -> ttn._any
          ? make_from( tn._any, tn._nil, tn._sub )
          : TypeNil.make(false,_nil&tn._nil,_sub&tn._sub);
      };
    } else {
      // Low union, subclasses fall "into" the Union.
      boolean nil = _nil & tn._nil;
      boolean sub = _sub & tn._sub;
      // If type would fall to subtype YES-nil, fall to AND-nil instead.
      nil &= sub;
      TypeInt    int0= _int.make_from(false, nil, _int._sub & tn._sub );
      TypeFlt    flt = _flt.make_from(false, nil, _flt._sub & tn._sub );
      TypeMemPtr tmp = _tmp.make_from(false, nil, _tmp._sub & tn._sub );
      TypeFunPtr tfp = _tfp.make_from(false, nil, _tfp._sub & tn._sub );
      return switch (tn) {
      case TypeInt    tint -> make(false, nil, sub, (TypeInt   )int0.meet(tint), flt, tmp, tfp );
      case TypeFlt    tflt -> make(false, nil, sub, int0, (TypeFlt   )flt.meet(tflt), tmp, tfp );
      case TypeMemPtr ttmp -> make(false, nil, sub, int0, flt, (TypeMemPtr)tmp.meet(ttmp), tfp );
      case TypeFunPtr ttfp -> make(false, nil, sub, int0, flt, tmp, (TypeFunPtr)tfp.meet(ttfp) );
      case TypeRPC    trpc -> TypeNil.make(false,nil,sub); // TODO: expand and allow
      case TypeNil    ttn  -> ttn._any
        ? make(false, nil, sub, int0, flt, tmp, tfp )
        : TypeNil.make(false,_nil&tn._nil,sub);
      };
    }
  }

  boolean and_sub() {
    return _any ? _sub & _int._sub & _flt._sub & _tmp._sub & _tfp._sub : _sub;
  }
}
