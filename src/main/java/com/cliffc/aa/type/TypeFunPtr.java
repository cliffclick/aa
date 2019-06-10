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
  public TypeTuple _ts;         // Arg types; 1-based, 0 reserved for the memory argument
  public Type _ret;             // return types
  TypeMem _retmem;              // return MEMORY types
  // List of known functions in set, or 'flip' for choice-of-functions.
  private BitsFun _fidxs;       // Known function bits

  private TypeFunPtr(TypeTuple ts, Type ret, TypeMem retmem, BitsFun fidxs ) { super(TFUNPTR); init(ts,ret,retmem,fidxs); }
  private void init (TypeTuple ts, Type ret, TypeMem retmem, BitsFun fidxs ) {
    _ts = ts;
    _ret = ret;
    _retmem = retmem;
    _fidxs = fidxs;
    assert ts==null || ts.at(0) instanceof TypeMem; // argmem in argument#0
  }
  @Override int compute_hash() {
    int hash = TFUNPTR +
      (_ts==null ? -99 : _ts._hash) +
      _ret   ._hash +
      _retmem._hash +
      _fidxs ._hash;
    return hash;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    return _ts==tf._ts && _ret==tf._ret && _retmem==tf._retmem && _fidxs==tf._fidxs;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    SB sb = FunNode.names(_fidxs,new SB());
    if( _ts==null ) return sb.p("{forward_ref}").toString();
    sb.p('{');
    int nargs = nargs();
    if( nargs > 0 && _ts.at(0)!=TypeMem.XMEM ) sb.p(_ts.at(0).str(dups)).p(' ');
    for( int i=1; i<Math.min(4,nargs); i++ ) sb.p(_ts.at(i).str(dups)).p(' ');
    if( nargs > 4 ) sb.p("...");
    sb.p("-> ").p(_ret.str(dups));
    if( _retmem != TypeMem.XMEM ) // Return memory is only interesting if returning something special
      sb.p(' ').p(_retmem.str(dups));
    return sb.p('}').toString();
  }

  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr ret ) { FREE=this; return ret; }
  static TypeFunPtr make_new( TypeTuple ts, Type ret, TypeMem retmem, int parent_fidx ) {
    return make(ts,ret,retmem,BitsFun.make_new_fidx(parent_fidx));
  }
  public static TypeFunPtr make( TypeTuple ts, Type ret, TypeMem retmem, BitsFun fidxs ) {
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(ts,ret,retmem,fidxs);
    else {   FREE = null;        t1.init(ts,ret,retmem,fidxs); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  
  static TypeFunPtr any1( int fidx ) {
    return make(TypeTuple.SCALAR1,Type.SCALAR,TypeMem.MEM, BitsFun.make0(fidx));
  }
  static TypeFunPtr any2() {
    return make(TypeTuple.SCALAR2,Type.SCALAR,TypeMem.MEM, BitsFun.FULL);
  }

  private static final TypeTuple GENERIC_ARGS=TypeTuple.XSCALARS;
  private static final Type      GENERIC_RET =Type.SCALAR; // Can return almost anything
  public  static final TypeFunPtr GENERIC_FUNPTR = make_generic();
  private static final TypeFunPtr FUNPTR1 = any1(1); // Only for testing
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{FUNPTR1,GENERIC_FUNPTR};
  
  @Override protected TypeFunPtr xdual() {
    return new TypeFunPtr((TypeTuple)_ts.dual(),
                          _ret.dual(),
                          _retmem.dual(),
                          _fidxs.dual());
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
    Type ret = _ret.meet(tf._ret);
    TypeMem retmem = (TypeMem)_retmem.meet(tf._retmem);
    return make(ts,ret,retmem,fidxs);
  }

  public final int nargs() { return _ts._ts.length; }
  public final Type arg(int idx) { return _ts.at(idx); }
  public final Type ret() { return _ret; }

  @Override public boolean above_center() { return _fidxs.above_center(); }
  // Fidxes represent a single function and thus are constants.
  @Override public boolean may_be_con()   { return is_con() || above_center(); }
  @Override public boolean is_con()       { return _fidxs.abit()!=-1; }
  @Override public boolean must_nil() { return _fidxs.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make(_ts,_ret,_retmem,bits);
  }
  @Override public Type meet_nil() {
    if( _fidxs.test(0) )      // Already has a nil?
      return _fidxs.above_center() ? TypeNil.NIL : this;
    return make(_ts,_ret,_retmem,_fidxs.meet(BitsFun.NIL));
  }
      
  // Return true if this is an ambiguous function pointer
  public boolean is_ambiguous_fun() { return above_center(); }
  public int fidx() { return _fidxs.getbit(); }

  // Generic functions
  public boolean is_forward_ref()             { return _ts==null; }
  public static TypeFunPtr make_forward_ref() { return make(null, GENERIC_RET,TypeMem.MEM, BitsFun.make_new_fidx(BitsFun.ALL)); }
  private static TypeFunPtr make_generic()    { return make(GENERIC_ARGS, GENERIC_RET,TypeMem.MEM, BitsFun.FULL); }
  // Iterate over any nested child types
  @SuppressWarnings("unchecked")
  @Override public void iter( Consumer<Type> c ) { _ts.iter(c); c.accept(_ret); }
  @Override boolean hasBits(BitSet bs) { return BitsFun.HASHMAKER.has_bits(_fidxs); }
}
