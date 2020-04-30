package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

// Function signatures: formal arguments (and return) used to type-check.  This
// is NOT any "code pointer" or "function index" or "fidx"; see TypeFunPtr.
public final class TypeFunSig extends Type<TypeFunSig> {
  public TypeStruct _formals;
  public Type _ret;
  
  private TypeFunSig(TypeStruct formals, Type ret ) { super(TFUNSIG); init(formals,ret); }
  private void init (TypeStruct formals, Type ret ) { _formals=formals; _ret=ret; }
  @Override int compute_hash() { assert _formals._hash != 0;  return TFUNSIG + _formals._hash + _ret._hash; }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFunSig) ) return false;
    TypeFunSig tf = (TypeFunSig)o;
    return _formals==tf._formals && _ret==tf._ret;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  
  @Override public String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    return _formals+" -> "+_ret;
  }

  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    _formals.dstr(sb,dups);
    sb.p("->");
    _ret.dstr(sb,dups);
    return sb;
  }

  private static TypeFunSig FREE=null;
  @Override protected TypeFunSig free( TypeFunSig ret ) { FREE=this; return ret; }
  public static TypeFunSig make( TypeStruct formals, Type ret ) {
    assert formals._ts[0].is_display_ptr() && ret.isa(SCALAR);
    TypeFunSig t1 = FREE;
    if( t1 == null ) t1 = new TypeFunSig(formals,ret);
    else {   FREE = null;        t1.init(formals,ret); }
    TypeFunSig t2 = (TypeFunSig)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static final TypeFunSig II_I = make(TypeStruct.INT64_INT64,TypeInt.INT64);
  static final TypeFunSig[] TYPES = new TypeFunSig[]{II_I};

  @Override protected TypeFunSig xdual() { return new TypeFunSig(_formals.dual(),_ret.dual()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TFUNSIG: break;
    case TFLT:
    case TFUNPTR:
    case TINT:
    case TMEM:
    case TMEMPTR:
    case TOBJ:
    case TRPC:
    case TSTR:
    case TSTRUCT:
    case TTUPLE:
      return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeFunSig tf = (TypeFunSig)t;
    return make((TypeStruct)_formals.meet(tf._formals),_ret.meet(tf._ret));
  }

  @Override public boolean above_center() { return _formals.above_center(); }
  @Override public boolean may_be_con()   { return above_center(); }
  @Override public boolean is_con()       { return false; }
  @Override public boolean must_nil()     { return false; }
  @Override public boolean may_nil()      { return false; }
  @Override Type not_nil() { return this; }
  @Override public Type meet_nil(Type nil) { return Type.SCALAR; }
  @Override public byte isBitShape(Type t) { return 99; }
}
