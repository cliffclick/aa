package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;

/** A Tuple with exactly 4 fields:
 *  0 - Function exit control
 *  1 - Function exit value type
 *  2 - Function RPC type (set of callers) - Short cut available type, to avoid
 *      going to the FunNode and reversing to the RPC.
 *  3 - Function signature, with a single FIDX 
 * 
 *  This is the type of EpilogNodes, except they also have a _fidx to map to
 *  the FunNode (used when the FunNode is collapsing) AND a pointer to the
 *  FunNode.
*/
public class TypeFunPtr extends TypeTuple<TypeFunPtr> {
  private TypeFunPtr( byte nil, Type[] ts, Type inf ) {
    super(nil,ts,inf,TFUNPTR);
    init(nil,ts,inf);
  }
  protected void init( byte nil, Type[] ts, Type inf ) {
    super.init(nil,ts,inf,TFUNPTR);
    assert is_fun_ptr();
  }
  
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeFunPtr && eq((TypeFunPtr)o);
  }    
  
  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr f ) { assert f._type==TFUNPTR; FREE=f; return this; }
  private static TypeFunPtr make0( byte nil, Type[] ts, Type inf ) {
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(nil,ts,inf);
    else { FREE = null; t1.init(nil,ts,inf); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  
  public static TypeFunPtr make0( Type ctrl, Type ret, TypeRPC rpc, TypeFun fun ) {
    return make0(NOT_NIL, new Type[] {ctrl,ret,rpc,fun}, Type.ALL);
  }
  public static TypeFunPtr make( TypeFun fun ) { return make0(Type.CTRL,fun._ret,TypeRPC.ALL_CALL, fun); }
  public static TypeFunPtr make( int fidx ) { return make(FunNode.find_fidx(fidx)._tf); }
  public static TypeFunPtr make( TypeTuple tt ) { return make0(tt._nil,tt._ts,tt._inf); }

  public static final TypeFunPtr FUNPTR1     = make(TypeFun.any(1,-1));
  public static final TypeFunPtr FUNPTR2     = make(TypeFun.any(2,-1));
  public static final TypeFunPtr GENERIC_FUN = make(TypeFun.make_generic());
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{FUNPTR2,GENERIC_FUN};
  
  // The length of Tuples is a constant, and so is its own dual.  Otherwise
  // just dual each element.  Also flip the infinitely extended tail type.
  @Override protected TypeFunPtr xdual() {
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeFunPtr(xdualnil(),ts,_inf.dual());
  }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE: 
    case TFUNPTR: break;
    case TSTR:   return TypeOop.make(nmeet(((TypeNullable)t)._nil),false);
    case TFLT:
    case TINT:
    case TRPC:
    case TFUN:   return Type.SCALAR;
    case TOOP:
    case TSTRUCT: 
    case TERROR:
    case TNAME:
    case TUNION: return t.xmeet(this); // Let other side decide
    default: throw typerr(t);
    }
    // Length is longer of 2 tuples.  Shorter elements take the meet; longer
    // elements meet the shorter extension.
    TypeTuple tt = (TypeTuple)t;
    TypeTuple rez = _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
    return rez.is_fun_ptr() ? make(rez) : rez; // Copy back up to a TypeFunPtr
  }
  // Make a subtype with a given nil choice
  @Override public Type make_nil(byte nil) { return make0(nil,_ts,_inf); }

  // Return true if this is a forward-ref function pointer (return type from EpilogNode)
  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }

  public Type    ctl() { return          _ts[0]; }
  public Type    val() { return          _ts[1]; }
  public TypeFun fun() { return (TypeFun)_ts[3]; }
  // Return an error message, if any exists
  @Override public String errMsg() {
    // Ok to have a function which cannot be executed
    return null;
  }
}
