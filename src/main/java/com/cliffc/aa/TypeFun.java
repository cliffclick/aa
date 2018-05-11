package com.cliffc.aa;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

// Function constants
public class TypeFun extends Type {
  public TypeTuple _ts;         // Arg types
  public Type _ret;             // return types
  // List of known functions in set, or 'flip' for choice-of-functions
  public Bits _fidxs;         // 

  private TypeFun( TypeTuple ts, Type ret, Bits fidxs ) { super(TFUN); init(ts,ret,fidxs); }
  private void init(TypeTuple ts, Type ret, Bits fidxs ) { _ts = ts; _ret = ret; _fidxs = fidxs; }
  @Override public int hashCode( ) { return TFUN + _ts.hashCode() + _ret.hashCode()+ _fidxs.hashCode();  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFun) ) return false;
    TypeFun tf = (TypeFun)o;
    return _ts==tf._ts && _ret==tf._ret && _fidxs==tf._fidxs;
  }
  @Override public String toString() {
    return str(_fidxs.toString(new SB())).toString();
  }
  public SB str( SB sb ) {
    sb.p('{');
    for( Type t : _ts._ts ) sb.p(t.toString()).p(' ');
    return sb.p("-> ").p(_ret.toString()).p('}');
  }
  
  private static TypeFun FREE=null;
  private TypeFun free( TypeFun f ) { FREE=f; return this; }
  public static TypeFun make( TypeTuple ts, Type ret, int fidx ) { return make(ts,ret,Bits.make(fidx)); }
  public static TypeFun make( TypeTuple ts, Type ret, Bits fidxs ) {
    TypeFun t1 = FREE;
    if( t1 == null ) t1 = new TypeFun(ts,ret,fidxs);
    else { FREE = null; t1.init(ts,ret,fidxs); }
    TypeFun t2 = (TypeFun)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  public static TypeFun any( int nargs, int fidx ) {
    Bits bs = fidx==-1 ? Bits.FULL : Bits.make(fidx);
    switch( nargs ) {
    case 0: return make(TypeTuple.ANY    ,Type.SCALAR, bs);
    case 1: return make(TypeTuple.SCALAR ,Type.SCALAR, bs);
    case 2: return make(TypeTuple.SCALAR2,Type.SCALAR, bs);
    default: throw AA.unimpl();
    }
  }

  static final TypeFun[] TYPES = new TypeFun[]{any(0,-1),any(1,-1),any(2,-1)};
  
  @Override protected TypeFun xdual() { return new TypeFun((TypeTuple)_ts.dual(),_ret.dual(),_fidxs.flip()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TCONTROL:
    case TTUPLE: return TypeErr.ALL;
    case TFLT:
    case TINT:
    case TSTR:   return Type.SCALAR;
    case TFUN:   break;
    case TUNION: return t.xmeet(this); // Let TypeUnion decide
    default: throw typerr(t);   // All else should not happen
    }
    TypeFun tf = (TypeFun)t;
    // If either set includes the others functions, use the meet of args+ret.
    // If the sets do not properly subset, go to a union.
    Bits fidxs = _fidxs.or( tf._fidxs );
    if( fidxs!=_fidxs && fidxs!=tf._fidxs )
      return TypeUnion.make(false,this,tf); // Non-overlapping, go to a union
    TypeTuple ts = (TypeTuple)_ts.meet(tf._ts);
    Type ret = _ret.meet(tf._ret);
    return make(ts,ret,fidxs);
  }
  
  @Override public Type ret() { return _ret; }

  @Override protected boolean canBeConst() { throw AA.unimpl(); }

  public int fidx() { return _fidxs.getbit(); }
  FunNode funode() { return (FunNode)(FunNode.get(fidx()).at(0).at(2)); }
  
  // Filter out function types with incorrect arg counts
  @Override public Type filter(int nargs) { return _ts._ts.length==nargs ? this : null; }
  // Operator precedence
  @Override public byte op_prec() { return funode().op_prec(); } 
}
