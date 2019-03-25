package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;

/** A Tuple with exactly 4 fields:
 *  0 - Function exit control
 *  1 - Function exit value type
 *  2 - Function RPC type (set of callers) - Short cut available type, to avoid
 *      going to the FunNode and reversing to the RPC.
 *  3 - Function signature, with a single FIDX 
 * 
 *  This is the type of EpilogNodes, and is somewhat redundant because they
 *  also have a _fidx to map to the FunNode (used when the FunNode is
 *  collapsing) AND a pointer to the FunNode.
*/
public class TypeFun extends TypeTuple<TypeFun> {
  private TypeFun( boolean any, Type[] ts ) {
    super(TFUN, any, ts);
    init(any,ts);
  }
  protected void init( boolean any, Type[] ts ) {
    super.init(TFUN, any, ts);
    assert is_fun();
  }
  
  @Override public boolean equals( Object o ) { return o instanceof TypeFun && super.equals(o); }    
  
  private static TypeFun FREE=null;
  @Override protected TypeFun free( TypeFun ret ) { FREE=this; return ret; }
  private static TypeFun make( boolean any, Type[] ts ) {
    // TODO: assert fun().is_con() or _ts[3]._fidxes.is_con()
    TypeFun t1 = FREE;
    if( t1 == null ) t1 = new TypeFun(any,ts);
    else { FREE = null; t1.init(any,ts); }
    assert t1._type==TFUN;
    TypeFun t2 = (TypeFun)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  
  public static TypeFun make( Type ctrl, Type ret, Type rpc, TypeFunPtr fun ) {
    return make(false,new Type[]{ctrl,ret,rpc,fun});
  }
  public static TypeFun make( TypeFunPtr fun ) { return make(Type.CTRL,fun._ret,TypeRPC.ALL_CALL, fun); }
  public static TypeFun make( int fidx ) { return make(FunNode.find_fidx(fidx)._tf); }

         static final TypeFun FUN1        = make(TypeFunPtr.any(1, 0)); // Some 1-arg function
  public static final TypeFun FUN2        = make(TypeFunPtr.any(2,-1)); // Some 2-arg function
  public static final TypeFun GENERIC_FUN = make(TypeFunPtr.GENERIC_FUNPTR); // For EpilogNode default type
  static final TypeFun[] TYPES = new TypeFun[]{FUN1,FUN2};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeFun xdual() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeFun(!_any,ts);
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TFUN: break;
    case TNAME:
    case TSTR:
    case TFLT:
    case TINT:
    case TTUPLE: 
    case TFUNPTR:
    case TMEMPTR:
    case TSTRUCT:
    case TRPC:
    case TNIL:
    case TMEM:   return ALL;
    default: throw typerr(t);
    }
    TypeFun tt = (TypeFun)t;
    assert _ts.length==tt._ts.length;
    Type[] ts = new Type[4];
    for( int i=0; i<_ts.length; i++ )  ts[i] = _ts[i].meet(tt._ts[i]);
    return make(_any&tt._any,ts);
  }

  // Return true if this is a forward-ref function pointer (return type from EpilogNode)
  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }

  public Type ctl() { return _ts[0]; }
  public Type val() { return _ts[1]; }
  public Type rpc() { return _ts[2]; }
  public TypeFunPtr fun() { return (TypeFunPtr)_ts[3]; }
  @Override boolean must_nil() { return false; }
  @Override Type not_nil() { return this; }
}
