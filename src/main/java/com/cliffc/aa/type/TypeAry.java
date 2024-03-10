package com.cliffc.aa.type;

import com.cliffc.aa.util.*;
  
import java.util.function.*;

import static com.cliffc.aa.AA.TODO;

// A Cyclic Type where fields are indexed by dynamic integer.  Probably becomes
// a specialized field type for TypeStruct, allowed only as the last field.
public class TypeAry extends Type<TypeAry> implements Cyclic {
  public  TypeInt _len;         // Count of elements
  private Type _elem;           // MEET over all elements.
  private Type _stor;           // Storage class; widened over elements.  Can be, e.g. bits or complex structs with embedded pointers

  private TypeAry init(TypeInt len, Type elem, Type stor ) {
    super.init();
    _len  = len;
    _elem = elem;
    _stor = stor;
    return this;
  }
  @Override public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) {
    //return map.apply(_t);
    throw TODO();
  }
  @Override public long lwalk( LongStringFunc map, LongOp reduce ) { return map.run(_elem,"elem"); }
  @Override public void walk( TypeStrRun map ) { map.run(_elem,"elem"); }
  @Override public void walk_update( TypeMap map ) { throw TODO(); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) { throw TODO(); }

  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_len._hash,_elem._type,_stor._type); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeAry ta) || !super.equals(o) ) return false;
    return _len == ta._len && _elem == ta._elem && _stor == ta._stor;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override PENV _str0( PENV P ) {
    P.p('[');
    if( _len!=null && _len != TypeInt.INT64 ) _len._str(P);
    P.p(']');
    if( _elem !=null ) _elem._str(P);
    if( _elem != _stor && _stor!=null ) _stor._str(P.p('/'));
    return P;
  }

  static { new Pool(TARY,new TypeAry()); }
  public static TypeAry make( TypeInt len, Type elem, Type stor ) {
    TypeAry t1 = POOLS[TARY].malloc();
    return t1.init(len,elem,stor).hashcons_free();
  }

  public static final TypeAry ARY   = make(TypeInt.INT64 ,TypeNil.SCALAR ,TypeStruct.ISUSED );
  public static final TypeAry ARY0  = make(TypeInt.INT64 ,TypeNil.NIL    ,TypeStruct.ISUSED );
  public static final TypeAry BYTES = make(TypeInt.con(3),TypeInt.INT8   ,TypeStruct.ISUSED );
  static final TypeAry[] TYPES = new TypeAry[]{ARY,ARY0,BYTES};

  @Override protected TypeAry xdual() { return POOLS[TARY].<TypeAry>malloc().init(_len.dual(),_elem.dual(),_stor.dual()); }
  @Override void rdual() {
    _dual._len  = _len ._dual;
    _dual._elem = _elem._dual;
    _dual._stor = _stor._dual;
  }
  @Override protected Type xmeet( Type t ) {
    TypeAry ta = (TypeAry)t;
    TypeInt size = (TypeInt)_len.meet(ta._len);
    Type elem = _elem.meet(ta._elem);
    Type stor = _stor.meet(ta._stor);
    return make(size,elem,stor);
  }

  // Type at a specific index
  public Type ld(TypeInt idx) { return _elem; }
  public TypeAry update(TypeInt idx, Type val) {
    throw TODO();
  }
  @Override BitsFun _all_reaching_fidxs( TypeMem tmem ) {
    return _elem._all_reaching_fidxs(tmem);
  }
  @Override public boolean above_center() { return _elem.above_center(); }
}
