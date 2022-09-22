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

// Since contains a TMP (and TFP), must implement Cyclic and participates in
// cyclic type construction.
public class TypeUnion extends Type<TypeUnion> implements Cyclic {
  private boolean    _any;
  private TypeInt    _int;
  private TypeFlt    _flt;
  private TypeMemPtr _tmp;
  private TypeFunPtr _tfp;
  
  protected TypeUnion init( boolean any, TypeInt int0, TypeFlt flt, TypeMemPtr tmp, TypeFunPtr tfp ) {
    super.init();
    boolean n = int0._nil, s = int0._sub;
    assert n==flt._nil && n==tmp._nil && n==tfp._nil; // Internal nil flags all align
    assert s==flt._sub && s==tmp._sub && s==tfp._sub;    
    _any = any;
    _int = int0;
    _flt = flt;
    _tmp = tmp;
    _tfp = tfp;
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
      _any==t._any &&
      _int==t._int &&
      _flt==t._flt &&
      _tmp==t._tmp &&
      _tfp==t._tfp;
  }
  // Never part of a cycle so the normal equals works
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeUnion tu) ) return false;
    if( !super.equals(tu) || _any != tu._any ) return false;
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
    return sb.p(" ]");
  }
  
  static TypeUnion valueOf(Parse P, String cid, boolean any) {
    P.require('&');
    P.require('[');
    TypeInt int0= (TypeInt   )P.type();   P.require(any ? '+' : '&');
    TypeFlt flt = (TypeFlt   )P.type();   P.require(any ? '+' : '&');
    TypeUnion  tu  = malloc(any,int0,flt,null,null);
    if( cid!=null ) P._dups.put(cid,tu);
    tu._tmp = (TypeMemPtr)P.type();   P.require(any ? '+' : '&');
    tu._tfp = (TypeFunPtr)P.type();
    P.require(']');
    if( P.peek('?') )
      tu = (TypeUnion)tu.meet(TypeNil.XNIL);
    return tu;
  }

  static { new Pool(TUNION,new TypeUnion()); }
  private static TypeUnion malloc( boolean any, TypeInt int0, TypeFlt flt, TypeMemPtr tmp, TypeFunPtr tfp ) {
    TypeUnion t1 = POOLS[TUNION].malloc();
    return t1.init(any,int0,flt,tmp,tfp);
  }

  public static TypeUnion make( boolean any, TypeInt int0, TypeFlt flt, TypeMemPtr tmp, TypeFunPtr tfp ) { return malloc(any,int0,flt,tmp,tfp).hashcons_free(); }

  public TypeInt    _int() { return _int; }
  public TypeFlt    _flt() { return _flt; }
  public TypeMemPtr _tmp() { return _tmp; }
  public TypeFunPtr _tfp() { return _tfp; }
  
  public static final TypeUnion TEST1 = make(true ,TypeInt.NINT64.dual(),TypeFlt.PI   ,TypeMemPtr.ISUSED.dual(),TypeFunPtr.GENERIC_FUNPTR.dual());
  public static final TypeUnion TEST2 = make(false,TypeInt.INT8         ,TypeFlt.FLT64,TypeMemPtr.ISUSED0      ,TypeFunPtr.THUNK                );
  static final TypeUnion[] TYPES = new TypeUnion[]{TEST1.dual(),TEST2};

  // The length of Tuples is a constant, and so is its own dual.  Otherwise,
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeUnion xdual() {
    return malloc(!_any, _int.dual(), _flt.dual(), _tmp.dual(), _tfp.dual());
  }
  void rdual() { throw unimpl(); }

  // Meet 2 Unions together
  @Override protected TypeUnion xmeet( Type t ) {
    TypeUnion tu = (TypeUnion)t;
    return make(_any & tu._any,
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
        case TypeRPC    trpc -> trpc;
        case TypeNil    ttn  -> ttn._any       
          ? nil_meet(ttn)     // High TypeNil folds into every member
          : meet_nil(ttn);    // Low  TypeNil folds every member into a TypeNil
      };
    } else {
      // Low union, subclasses fall "into" the Union.
      // If type would fall to subtype YES-nil, fall to AND-nil instead.
      //  nil &= sub;
      TypeUnion tu = nil_meet(tn);

      return switch (tn) {
        case TypeInt    tint -> make(false, (TypeInt   )tu._int.meet(tint), tu._flt, tu._tmp, tu._tfp );
        case TypeFlt    tflt -> make(false, tu._int, (TypeFlt   )tu._flt.meet(tflt), tu._tmp, tu._tfp );
        case TypeMemPtr ttmp -> make(false, tu._int, tu._flt, (TypeMemPtr)tu._tmp.meet(ttmp), tu._tfp );
        case TypeFunPtr ttfp -> make(false, tu._int, tu._flt, tu._tmp, (TypeFunPtr)tu._tfp.meet(ttfp) );
        case TypeRPC    trpc -> this;
        case TypeNil    ttn  -> ttn._any
        ? tu                  // High TypeNil folds into every member
        : meet_nil(ttn);      // Low  TypeNil folds every member into a TypeNil
      };
    }
  }
  // Spray a TypeNil across all members, returning a TypeUnion
  private TypeUnion nil_meet(TypeNil tn) {
    return make(_any,
                _int.make_from(_int._any,_int._nil&tn._nil,_int._sub&tn._sub),
                _flt.make_from(_flt._any,_flt._nil&tn._nil,_flt._sub&tn._sub),
                _tmp.make_from(_tmp._any,_tmp._nil&tn._nil,_tmp._sub&tn._sub),
                _tfp.make_from(_tfp._any,_tfp._nil&tn._nil,_tfp._sub&tn._sub));
  }
  // Fold all members into a low TypeNil.  Can only be SCALAR or NSCALR
  private TypeNil meet_nil(TypeNil tn) {
    return (TypeNil)tn.meet(_int).meet(_flt).meet(_tmp).meet(_tfp);
  }

  @Override public boolean above_center() { return _any; }
}
