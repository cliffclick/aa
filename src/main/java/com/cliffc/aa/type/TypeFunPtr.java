package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;

import java.util.BitSet;
import java.util.function.Consumer;

// Function constants and signatures.  Contrast this to 'TypeFun'.
// A single instance can include all possible aliased function pointers.
// Function pointers can be executed, are not GC'd, and cannot be
// Loaded or Stored through (although they can be loaded & stored).
public final class TypeFunPtr extends Type<TypeFunPtr> {
  public TypeTuple _ts;         // Arg types
  public Type _argmem;          // Argument MEMORY types
  public Type _ret;             // return types
  public Type _retmem;          // return MEMORY types
  // List of known functions in set, or 'flip' for choice-of-functions.
  public BitsFun _fidxs;        // Known function bits
  public int _nargs;            // Count of args or -1 for forward_ref

  private TypeFunPtr(TypeTuple ts, Type argmem, Type ret, Type retmem, BitsFun fidxs, int nargs ) { super(TFUNPTR); init(ts,argmem,ret,retmem,fidxs,nargs); }
  private void init (TypeTuple ts, Type argmem, Type ret, Type retmem, BitsFun fidxs, int nargs ) {
    _ts = ts;
    _argmem = argmem;
    _ret = ret;
    _retmem = retmem;
    _fidxs = fidxs;
    _nargs=nargs;
  }
  @Override public int hashCode( ) { return
      TFUNPTR +
      _ts.hashCode() +
      _argmem.hashCode() +
      _ret.hashCode() +
      _retmem.hashCode() +
      _fidxs.hashCode() +
      _nargs;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    return _ts==tf._ts && _argmem==tf._argmem && _ret==tf._ret && _retmem==tf._retmem && _fidxs==tf._fidxs && _nargs==tf._nargs;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    SB sb = FunNode.names(_fidxs,new SB());
    if( _nargs==-1 ) return sb.p("{forward_ref}").toString();
    sb.p('{');
    for( int i=0; i<_ts._ts.length; i++ ) sb.p(arg(i).str(dups)).p(' ');
    if( _nargs==99 ) sb.p("... ");
    sb.p(_argmem.str(dups));
    sb.p("-> ").p(_ret.str(dups)).p(_retmem.str(dups)).p('}');
    return sb.toString();
  }

  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr ret ) { FREE=this; return ret; }
  public static TypeFunPtr make( TypeTuple ts, Type argmem, Type ret, Type retmem, int  fidx , int nargs ) { return make(ts,argmem,ret,retmem,BitsFun.make0(fidx),nargs); }
  public static TypeFunPtr make( TypeTuple ts, Type argmem, Type ret, Type retmem, BitsFun fidxs, int nargs ) {
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(ts,argmem,ret,retmem,fidxs,nargs);
    else {   FREE = null;        t1.init(ts,argmem,ret,retmem,fidxs,nargs); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeFunPtr any( int nargs, int fidx ) {
    BitsFun bs = fidx==-1 ? BitsFun.FULL : BitsFun.make0(fidx);
    switch( nargs ) {
    case 0: return make(TypeTuple.SCALAR0,TypeMem.MEM,Type.SCALAR,TypeMem.MEM, bs,nargs);
    case 1: return make(TypeTuple.SCALAR1,TypeMem.MEM,Type.SCALAR,TypeMem.MEM, bs,nargs);
    case 2: return make(TypeTuple.SCALAR2,TypeMem.MEM,Type.SCALAR,TypeMem.MEM, bs,nargs);
    default: throw com.cliffc.aa.AA.unimpl();
    }
  }

  private static final TypeTuple GENERIC_ARGS=TypeTuple.XSCALARS;
  private static final Type      GENERIC_RET =Type.SCALAR; // Can return almost anything
  public  static final TypeFunPtr GENERIC_FUNPTR = make_generic();
  private static final TypeFunPtr FUNPTR1 = any(1,1);
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{FUNPTR1,GENERIC_FUNPTR};
  
  @Override protected TypeFunPtr xdual() {
    return new TypeFunPtr((TypeTuple)_ts.dual(),
                          _argmem.dual(),
                          _ret.dual(),
                          _retmem.dual(),
                          _fidxs.dual(),
                          _nargs);
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TFUNPTR:break;
    case TFLT:
    case TINT:
    case TMEMPTR:
    case TRPC:   return cross_nil(t);
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    case TFUN:
    case TTUPLE:
    case TOBJ:
    case TSTR:
    case TSTRUCT:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    // Join of args; meet of ret & fidxs
    TypeFunPtr tf = (TypeFunPtr)t;
    BitsFun fidxs = _fidxs.meet( tf._fidxs );
    TypeTuple ts = (TypeTuple)_ts.join(tf._ts);
    Type argmem = _argmem.join(tf._argmem);
    Type ret = _ret.meet(tf._ret);
    Type retmem = _retmem.meet(tf._retmem);
    int nargs = tf._ret.above_center()
      ? (_ret.above_center() ? Math.min(_nargs,tf._nargs) :   _nargs )
      : (_ret.above_center() ? tf._nargs : Math.max(_nargs,tf._nargs));
    return make(ts,argmem,ret,retmem,fidxs,nargs);
  }

  public final int nargs() { return _nargs; }
  public final Type arg(int idx) { return _ts.at(idx); }
  public final Type ret() { return _ret; }

  @Override public boolean above_center() { return _fidxs.above_center(); }
  @Override public boolean may_be_con()   { return _fidxs.is_con() || _fidxs.above_center(); }
  @Override public boolean is_con()       { return _fidxs.is_con(); }
  @Override public boolean must_nil() { return _fidxs.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    // Below center, return this; above center remove nil choice
    return above_center() && _fidxs.test(0) ? make(_ts,_argmem,_ret,_retmem,_fidxs.clear(0),_nargs) : this;
  }
  @Override public Type meet_nil() {
    if( _fidxs.test(0) )      // Already has a nil?
      return _fidxs.above_center() ? TypeNil.NIL : this;
    return make(_ts,_argmem,_ret,_retmem,_fidxs.meet(BitsFun.NIL),_nargs);
  }
      
  // Return true if this is an ambiguous function pointer
  public boolean is_ambiguous_fun() { return _fidxs.above_center(); }
  public int fidx() { return _fidxs.getbit(); }

  // Generic functions
  public boolean is_forward_ref()                    { return _nargs == -1; }
  public static TypeFunPtr make_forward_ref( int fidx ) { return make(GENERIC_ARGS, TypeMem.XMEM, GENERIC_RET,TypeMem.MEM, BitsFun.make0(fidx),-1); }
  private static TypeFunPtr make_generic()              { return make(GENERIC_ARGS, TypeMem.XMEM, GENERIC_RET,TypeMem.MEM, BitsFun.FULL,99); }
  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { _ts.iter(c); c.accept(_ret); }
}
