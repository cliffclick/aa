package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

// Function constants.  Contrast this to 'TypeTuple.make_fun_ptr'.
public class TypeFun extends Type<TypeFun> {
  public TypeTuple _ts;         // Arg types
  public Type _ret;             // return types
  // List of known functions in set, or 'flip' for choice-of-functions
  public Bits _fidxs;           //
  public int _nargs;            // Count of args or -1 for forward_ref

  private   TypeFun(TypeTuple ts, Type ret, Bits fidxs, int nargs ) { super(TFUN); init(ts,ret,fidxs,nargs); }
  private void init(TypeTuple ts, Type ret, Bits fidxs, int nargs ) { _ts = ts; _ret = ret; _fidxs = fidxs; _nargs=nargs; }
  @Override public int hashCode( ) { return TFUN + _ts.hashCode() + _ret.hashCode()+ _fidxs.hashCode() + _nargs;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFun) ) return false;
    TypeFun tf = (TypeFun)o;
    return _ts==tf._ts && _ret==tf._ret && _fidxs==tf._fidxs && _nargs==tf._nargs;
  }
  @Override public String toString() {
    return str(FunNode.names(_fidxs,new SB())).toString();
  }
  public SB str( SB sb ) {
    if( _nargs==-1 ) return sb.p("{forward_ref}");
    sb.p('{');
    for( int i=0; i<_nargs; i++ ) sb.p(arg(i).toString()).p(' ');
    return sb.p("-> ").p(_ret.toString()).p('}');
  }
  
  private static TypeFun FREE=null;
  @Override protected TypeFun free( TypeFun f ) { FREE=f; return this; }
  public static TypeFun make( TypeTuple ts, Type ret, int  fidx , int nargs ) { return make(ts,ret,Bits.make(fidx),nargs); }
  public static TypeFun make( TypeTuple ts, Type ret, Bits fidxs, int nargs ) {
    TypeFun t1 = FREE;
    if( t1 == null ) t1 = new TypeFun(ts,ret,fidxs,nargs);
    else {   FREE = null;     t1.init(ts,ret,fidxs,nargs); }
    TypeFun t2 = (TypeFun)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  public static TypeFun any( int nargs, int fidx ) {
    Bits bs = fidx==-1 ? Bits.FULL : Bits.make(fidx);
    switch( nargs ) {
    case 0: return make(TypeTuple.SCALAR0,Type.SCALAR, bs,nargs);
    case 1: return make(TypeTuple.SCALAR1,Type.SCALAR, bs,nargs);
    case 2: return make(TypeTuple.SCALAR2,Type.SCALAR, bs,nargs);
    default: throw com.cliffc.aa.AA.unimpl();
    }
  }

  static final TypeFun[] TYPES = new TypeFun[]{any(0,-1),any(1,-1),any(2,-1)};
  
  @Override protected TypeFun xdual() { return new TypeFun((TypeTuple)_ts.dual(),_ret.dual(),_fidxs.dual(),_nargs); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TCTRL:
    case TXCTRL: return Type.ALL;
    case TOOP:
    case TRPC:
    case TSTRUCT:
    case TTUPLE:
    case TFUNPTR:
    case TFLT:
    case TINT:
    case TSTR:   return Type.SCALAR;
    case TFUN:   break;
    case TERROR:
    case TNAME:
    case TUNION: return t.xmeet(this); // Let other side decide
    default: throw typerr(t);   // All else should not happen
    }
    // Join of args; meet of ret & fidxes
    TypeFun tf = (TypeFun)t;
    Bits fidxs = _fidxs.meet( tf._fidxs );
    TypeTuple ts = (TypeTuple)_ts.join(tf._ts);
    Type ret = _ret.meet(tf._ret);
    int nargs = tf._ret.above_center()
      ? (_ret.above_center() ? Math.min(_nargs,tf._nargs) :   _nargs )
      : (_ret.above_center() ? tf._nargs : Math.max(_nargs,tf._nargs));
    return make(ts,ret,fidxs,nargs);
  }

  public int nargs() { return _nargs; }
  @Override public Type arg(int idx) { return _ts.at(idx); }
  @Override public Type ret() { return _ret; }

  @Override public boolean above_center() { return _ret.above_center(); }
  @Override public boolean may_be_con()   { return _fidxs.abit() >= 0 || _fidxs.above_center(); }
  @Override public boolean is_con()       { return _fidxs.abit() >= 0; }
  // Return true if this type may BE a null.  Functions are not GC'd, are not
  // OOP's, and are never nil.
  @Override public boolean may_be_nil() { return false; }
  // Return true if this is an ambiguous function pointer
  @Override public boolean is_ambiguous_fun() { return _fidxs.above_center(); }
  public int fidx() { return _fidxs.getbit(); }

  // Generic functions
  private static final TypeTuple GENERIC_ARGS=TypeTuple.XSCALARS;
  private static final Type      GENERIC_RET =Type.SCALAR; // Can return almost anything
  public boolean is_forward_ref()                    { return _nargs == -1; }
  public static TypeFun make_forward_ref( int fidx ) { return make(GENERIC_ARGS, GENERIC_RET,Bits.make(fidx),-1); }
  public static TypeFun make_generic()               { return make(GENERIC_ARGS, GENERIC_RET,Bits.FULL,99); }
}
