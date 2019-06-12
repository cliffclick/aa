package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;

import java.util.BitSet;

// Function indices or function pointers; a single instance can include all
// possible aliased function pointers.  Function pointers can be executed, are
// not GC'd, and cannot be Loaded or Stored through (although they can be
// loaded & stored).  Each function index (or fidx) is a constant value, a
// classic code pointer.  Cloning the code immediately also clones the fidx
// with a new fidx bit for the new cloned copy.
//
// No other types, these are obtained from the function itself.  This is the
// type of EpilogNodes, and CallNodes get argument types from the FunNode via
// the Epilog, and return types directly from the Epilog.
public final class TypeFunPtr extends Type<TypeFunPtr> {
  // List of known functions in set, or 'flip' for choice-of-functions.
  private BitsFun _fidxs;       // Known function bits

  private TypeFunPtr(BitsFun fidxs ) { super(TFUNPTR); init(fidxs); }
  private void init (BitsFun fidxs ) { _fidxs = fidxs; }
  @Override int compute_hash() { return TFUNPTR + _fidxs ._hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunPtr) ) return false;
    TypeFunPtr tf = (TypeFunPtr)o;
    return _fidxs==tf._fidxs;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups) {
    int fidx = _fidxs.abit();
    if( fidx == -1 )
      return FunNode.names(_fidxs,new SB()).p("{...}").toString();
    FunNode fun = FunNode.find_fidx(fidx);
    return fun==null ? new SB().p('[').p(fidx).p(']').toString() : fun.xstr();
  }

  private static TypeFunPtr FREE=null;
  @Override protected TypeFunPtr free( TypeFunPtr ret ) { FREE=this; return ret; }
  public static TypeFunPtr make( BitsFun fidxs ) {
    TypeFunPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeFunPtr(fidxs);
    else {   FREE = null;        t1.init(fidxs); }
    TypeFunPtr t2 = (TypeFunPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  // Used by testing only
  static TypeFunPtr make_new() { return make(BitsFun.make_new_fidx(BitsFun.ALL)); }
  public BitsFun fidxs() { return _fidxs; }

  public  static final TypeFunPtr GENERIC_FUNPTR = make(BitsFun.make0(BitsFun.ALL)); // Only for testing
  static final TypeFunPtr[] TYPES = new TypeFunPtr[]{GENERIC_FUNPTR};
  
  @Override protected TypeFunPtr xdual() { return new TypeFunPtr(_fidxs.dual()); }
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
    return make(_fidxs.meet( ((TypeFunPtr)t)._fidxs ));
  }

  @Override public boolean above_center() { return _fidxs.above_center(); }
  // Fidxes represent a single function and thus are constants, but TypeFunPtrs
  // represent the execution of a function, and are never constants.
  @Override public boolean may_be_con()   { return false; }
  @Override public boolean is_con()       { return false; }
  @Override public boolean must_nil() { return _fidxs.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _fidxs.may_nil(); }
  @Override Type not_nil() {
    BitsFun bits = _fidxs.not_nil();
    return bits==_fidxs ? this : make(bits);
  }
  @Override public Type meet_nil() {
    if( _fidxs.test(0) )      // Already has a nil?
      return _fidxs.above_center() ? TypeNil.NIL : this;
    return make(_fidxs.meet(BitsFun.NIL));
  }

  // Generic functions
  public boolean is_forward_ref() { throw com.cliffc.aa.AA.unimpl(); }
  @Override boolean hasBits(BitSet bs) { return BitsFun.HASHMAKER.has_bits(_fidxs); }
}
