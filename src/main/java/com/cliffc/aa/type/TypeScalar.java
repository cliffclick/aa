package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

// Tracks escaped aliases and fidxs.
public final class TypeScalar extends TypeNil<TypeScalar> {
  public BitsAlias _aliases;
  public BitsFun   _fidxs;

  private TypeScalar init(boolean any, boolean nil, boolean sub, BitsAlias aliases, BitsFun fidxs ) {
    super.init(any, nil, sub);
    _aliases = aliases;
    _fidxs = fidxs;
    return this;
  }
  @Override protected TypeScalar _copy() {
    TypeScalar ti = super._copy();
    throw com.cliffc.aa.AA.unimpl();
  }

  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_aliases._hash,_fidxs._hash); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeScalar tf) ) return false;
    return super.equals(tf) && _aliases==tf._aliases && _fidxs==tf._fidxs;
  }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _any ) sb.p('~');
    _aliases.str(sb.p('%'));
    return _fidxs.str(sb);
  }
  static TypeScalar valueOf(Parse P, String cid, boolean any) {
    P.require('%');
    var aliases = P.bits(BitsAlias.EMPTY);
    var fidxs   = P.bits(BitsFun  .EMPTY);
    TypeScalar ts = make(any,any,any,aliases,fidxs);
    if( cid!=null ) P._dups.put(cid,ts);
    return ts;
  }
  
  static { new Pool(TSCALAR,new TypeScalar()); }
  private static TypeScalar malloc( boolean any, boolean nil, boolean sub, BitsAlias aliases, BitsFun fidxs ) {
    return POOLS[TSCALAR].<TypeScalar>malloc().init(any,nil,sub,aliases,fidxs);
  }
  private static TypeScalar make( boolean any, boolean nil, boolean sub, BitsAlias aliases, BitsFun fidxs ) {
    return malloc(any,nil,sub,aliases,fidxs).hashcons_free();
  }
  public static TypeScalar make( BitsAlias aliases, BitsFun fidxs ) { return make(false,false,false,aliases,fidxs); }
  @Override TypeScalar make_from( boolean nil, boolean sub ) { return make(_any,nil,sub,_aliases,_fidxs); }

  public static final TypeScalar INT = make(BitsAlias.INT,BitsFun.INT);
  static final TypeScalar EXT = make(BitsAlias.EXT,BitsFun.EXT);
  static final TypeScalar ALL = make(BitsAlias.NALL,BitsFun.NALL);
  static final TypeScalar[] TYPES = new TypeScalar[]{EXT,INT};

  @Override protected TypeScalar xdual() {
    boolean xor = _nil == _sub;
    return malloc(!_any,_nil^xor,_sub^xor,_aliases.dual(),_fidxs.dual());
  }
  @Override protected TypeScalar xmeet( Type t ) {
    TypeScalar ts = (TypeScalar)t;
    boolean any = _any & ts._any;
    boolean nil = _nil & ts._nil;
    boolean sub = _sub & ts._sub;
    return make(any,nil,sub,_aliases.meet(ts._aliases),_fidxs.meet(ts._fidxs));
  }

  // TypeScalar is in-between XSCALAR/high-TypeNil-subclasses, and SCALAR/low-TypeNil-subs
  final TypeNil smeet( TypeNil tn ) {
    // Parallel subclass of TypeNil (which right now means Int,Flt,MemPtr,FunPtr)
    assert !(tn instanceof TypeScalar) && tn.getClass() != TypeNil.class;

    return switch( tn ) {
    case TypeInt i -> _any ? i : this; // Above or below any TypeInt
    case TypeFlt f -> _any ? f : this; // Above or below any TypeFlt
    case TypeMemPtr tmp -> {
      BitsAlias aliases = tmp._aliases.meet(_aliases);
      yield _any ? tmp.make_from(aliases) : make(aliases,_fidxs);
    }
    case TypeFunPtr tfp -> {
      BitsFun fidxs = tfp.fidxs().meet(_fidxs);
      yield _any ? tfp.make_from(fidxs) : make(_aliases,fidxs);
    }
    default ->  throw unimpl();
    };
  }
  
}
