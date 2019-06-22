package com.cliffc.aa.type;

import java.util.BitSet;

// A simple function signature.  Not a function, nor a function-pointer.
public class TypeFun extends Type<TypeFun> {
  TypeTuple _args;
  Type _ret;
  private TypeFun    ( TypeTuple args, Type ret ) { super(TFUN); init(args,ret); }
  protected void init( TypeTuple args, Type ret ) { super.init(TFUN); _args = args; _ret=ret; }
  
  @Override int compute_hash() { return TFUN + _args._hash + _ret._hash; }
  @Override public boolean equals( Object o ) {
    return o instanceof TypeFun && _args==((TypeFun)o)._args && _ret==((TypeFun)o)._ret;
  }
  @Override String str( BitSet dups) { return _args.str(dups)+"-> "+_ret.str(dups); }
  
  private static TypeFun FREE=null;
  @Override protected TypeFun free( TypeFun ret ) { FREE=this; return ret; }
  public static TypeFun make( TypeTuple args, Type ret ) {
    TypeFun t1 = FREE;
    if( t1 == null ) t1 = new TypeFun(args,ret);
    else { FREE = null; t1.init(args,ret); }
    assert t1._type==TFUN;
    TypeFun t2 = (TypeFun)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static final TypeFun FUN1 = make(TypeTuple.SCALAR1,Type.SCALAR);
  static final TypeFun[] TYPES = new TypeFun[]{FUN1};
  
  @Override protected TypeFun xdual() { return new TypeFun((TypeTuple)_args.dual(),_ret.dual()); }
  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    if( t._type != TFUN ) return ALL;
    TypeFun tf = (TypeFun)t;
    return make((TypeTuple)_args.meet(tf._args),_ret.meet(tf._ret));
  }

  @Override public boolean above_center() { return _args.above_center(); }
  @Override public boolean must_nil() { return false; }
  @Override Type not_nil() { return this; }
  @Override public boolean may_be_con()   { return false; }
  @Override public boolean is_con()       { return false; }
}
