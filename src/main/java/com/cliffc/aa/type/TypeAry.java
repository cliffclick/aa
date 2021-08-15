package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

/**
 * A TypeObj where fields are indexed by dynamic integer.
 */
public class TypeAry extends TypeObj<TypeAry> {
  public  TypeInt _size;        // Count of elements
  private Type _elem;           // MEET over all elements.
  private TypeObj _stor;        // Storage class; widened over elements.  Can be, e.g. bits or complex structs with embedded pointers

  private TypeAry init(String name, boolean any, TypeInt sz, Type elem, TypeObj stor ) {
    super.init(TARY,name,any,any);
    _size = sz;
    _elem = elem;
    _stor = stor;
    return this;
  }
  @Override int compute_hash() { return super.compute_hash() + _size._hash + _elem._hash + _stor._hash;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeAry) || !super.equals(o) ) return false;
    TypeAry ta = (TypeAry)o;
    return _size == ta._size && _elem == ta._elem && _stor == ta._stor;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( _any ) sb.p('~');
    sb.p('[');
    if( _size!=null && _size != TypeInt.INT64 ) sb.p(_size);
    sb.p(']');
    if( _elem !=null ) sb.p(_elem);
    if( _elem != _stor && _stor!=null ) sb.p('/').p(_stor);
    return sb;
  }

  static { new Pool(TARY,new TypeAry()); }
  public static TypeAry make( String name, boolean any, TypeInt sz, Type elem, TypeObj stor ) {
    TypeAry t1 = POOLS[TARY].malloc();
    return t1.init(name,any,sz,elem,stor).hashcons_free();
  }

  public static TypeAry make( TypeInt sz, Type elem, TypeObj stor ) { return make("",false,sz,elem,stor); }
  public static final TypeAry ARY   = make("",false,TypeInt.INT64 ,Type.SCALAR ,TypeObj.OBJ );
  public static final TypeAry ARY0  = make("",false,TypeInt.INT64 ,Type.XNIL   ,TypeObj.OBJ );
  public static final TypeAry BYTES = make("",false,TypeInt.con(3),TypeInt.INT8,TypeObj.OBJ ); // TODO: TypeObjBits2
  static final TypeAry[] TYPES = new TypeAry[]{ARY,ARY0,BYTES};

  @Override protected TypeAry xdual() { return new TypeAry().init(_name, !_any,_size.dual(),_elem.dual(),(TypeObj)_stor.dual()); }
  @Override
  TypeAry rdual() {
    if( _dual != null ) return _dual;
    TypeAry dual = _dual = xdual();
    dual._dual = this;
    dual._hash = dual.compute_hash();
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TARY:   break;
    case TSTR:
    case TLIVE:
    case TSTRUCT:return OBJ;
    case TOBJ:   return t.xmeet(this);
    case TFUNSIG:
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
    boolean any = _any&ta._any;
    TypeInt size = (TypeInt)_size.meet(ta._size);
    Type elem = _elem.meet(ta._elem);
    TypeObj stor = (TypeObj)_stor.meet(ta._stor);
    return make("",any,size,elem,stor);
  }

  // Widen (lose info), to make it suitable as the default function memory.
  // All elements widened to SCALAR.
  @Override public TypeAry crush() {
    if( _any ) return this;     // No crush on high arrays
    return make(_size,Type.SCALAR,_stor);
  }

  public Type ld(TypeInt idx) {
    return _elem;
  }
  @Override public TypeObj update(TypeInt idx, Type val) {
    if( idx.above_center() ) return this; // Nothing updates
    if( val.isa(_elem) ) return this;     // No change
    Type elem = _elem.meet(val);          // Worse-case
    TypeInt size = _size; // TypeInt size = (TypeInt)_size.meet(idx); // CNC - Not inferring array size yet
    return make(size,elem,TypeObj.OBJ);
  }
  // Used during liveness propagation from Loads.
  // Fields not-loaded are not-live.
  @Override TypeAry remove_other_flds(String fld, Type live) {
    return ARY;
  }
}
