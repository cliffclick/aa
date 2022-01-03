package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.BiFunction;
import java.util.function.UnaryOperator;

import static com.cliffc.aa.AA.unimpl;

// A TypeObj where fields are indexed by dynamic integer.
public class TypeAry extends Type<TypeAry> implements Cyclic {
  public  TypeInt _len;         // Count of elements
  private Type _elem;           // MEET over all elements.
  private Type _stor;           // Storage class; widened over elements.  Can be, e.g. bits or complex structs with embedded pointers

  private TypeAry init(String name, TypeInt len, Type elem, Type stor ) {
    super.init(name);
    _len  = len;
    _elem = elem;
    _stor = stor;
    return this;
  }
  boolean _cyclic; // Type is cyclic.  This is a summary property, not a part of the type, hence is not in the equals nor hash
  @Override public boolean cyclic() { return _cyclic; }
  @Override public void set_cyclic() { _cyclic = true; }
  @Override public void walk1( BiFunction<Type,String,Type> map ) {
    //return map.apply(_t);
    throw com.cliffc.aa.AA.unimpl();
  }
  @Override public void walk_update( UnaryOperator<Type> update ) { throw com.cliffc.aa.AA.unimpl(); }

  @Override int compute_hash() { return super.compute_hash() + _len._hash + _elem._hash + _stor._hash;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeAry) || !super.equals(o) ) return false;
    TypeAry ta = (TypeAry)o;
    return _len == ta._len && _elem == ta._elem && _stor == ta._stor;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    sb.p('[');
    if( _len!=null && _len != TypeInt.INT64 ) sb.p(_len);
    sb.p(']');
    if( _elem !=null ) sb.p(_elem);
    if( _elem != _stor && _stor!=null ) sb.p('/').p(_stor);
    return sb;
  }

  static { new Pool(TARY,new TypeAry()); }
  public static TypeAry make( String name, TypeInt len, Type elem, Type stor ) {
    TypeAry t1 = POOLS[TARY].malloc();
    return t1.init(name,len,elem,stor).hashcons_free();
  }

  public static TypeAry make( TypeInt len, Type elem, Type stor ) { return make("",len,elem,stor); }
  public static final TypeAry ARY   = make("",TypeInt.INT64 ,Type.SCALAR ,TypeStruct.ISUSED );
  public static final TypeAry ARY0  = make("",TypeInt.INT64 ,Type.XNIL   ,TypeStruct.ISUSED );
  public static final TypeAry BYTES = make("",TypeInt.con(3),TypeInt.INT8,TypeStruct.ISUSED );
  static final TypeAry[] TYPES = new TypeAry[]{ARY,ARY0.dual(),BYTES};

  @Override protected TypeAry xdual() { return POOLS[TARY].<TypeAry>malloc().init(_name,_len.dual(),_elem.dual(),_stor.dual()); }
  @Override TypeAry rdual() {
    if( _dual != null ) return _dual;
    TypeAry dual = _dual = xdual();
    dual._dual = this;
    dual._hash = dual.compute_hash();
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TARY:   break;
    case TFLD:
    case TSTRUCT:
    case TTUPLE:
    case TFUNPTR:
    case TMEMPTR:
    case TFLT:
    case TINT:
    case TRPC:
    case TMEM:   return ALL;
    default: throw typerr(t);
    }
    TypeAry ta = (TypeAry)t;
    TypeInt size = (TypeInt)_len.meet(ta._len);
    Type elem = _elem.meet(ta._elem);
    Type stor = _stor.meet(ta._stor);
    return make("",size,elem,stor);
  }

  //// Widen (lose info), to make it suitable as the default function memory.
  //// All elements widened to SCALAR.
  //@Override public TypeAry crush() {
  //  if( _any ) return this;     // No crush on high arrays
  //  return make(_len,Type.SCALAR,_stor);
  //}

  // Type at a specific index
  public Type ld(TypeInt idx) { return _elem; }
  // Type over all elements
  public Type elem() { return _elem; }
  public Type stor() { return _stor; }
  public TypeAry update(TypeInt idx, Type val) {
  //  if( idx.above_center() ) return this; // Nothing updates
  //  if( val.isa(_elem) ) return this;     // No change
  //  Type elem = _elem.meet(val);          // Worse-case
  //  TypeInt size = _len; // TypeInt size = (TypeInt)_len.meet(idx); // CNC - Not inferring array size yet
  //  return make(size,elem,TypeStruct.OBJ);
    throw unimpl();
  }
  //// Used during liveness propagation from Loads.
  //// Fields not-loaded are not-live.
  //@Override TypeAry remove_other_flds(String fld, Type live) {
  //  return ARY;
  //}

  @Override BitsFun _all_reaching_fidxs( TypeMem tmem ) {
    return _elem._all_reaching_fidxs(tmem);
  }
  @Override public boolean above_center() { return _elem.above_center(); }
}
