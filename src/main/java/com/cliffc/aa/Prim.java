package com.cliffc.aa;

/** Function value */
public abstract class Prim {
  final static String[] ARGS1 = new String[]{"x"};
  final static String[] ARGS2 = new String[]{"x","y"};
  private static final TypeFun convInt32Flt64 = (TypeFun)new  ConvertInt32Flt64().hashcons();
  //private static final ValPrim1 convUInt32Int64 = new ConvertUInt32Int64();
  //private static final ValPrim1 convUInt32Flt64 = new ConvertUInt32Flt64();
  //private static final ValPrim1  convInt64Flt64 = new  ConvertInt64Flt64();
  
  static final TypeFun[] TYPES = new TypeFun[]{
    convInt32Flt64,

    (TypeFun)new MinusFlt64().hashcons(),
    (TypeFun)new    IDFlt64().hashcons(),
    (TypeFun)new MinusInt64().hashcons(),
    (TypeFun)new    IDInt64().hashcons(),
    (TypeFun)new AddFlt64  ().hashcons(),
    (TypeFun)new SubFlt64  ().hashcons(),
    (TypeFun)new MulFlt64  ().hashcons(),
    (TypeFun)new AddInt64  ().hashcons(),
    (TypeFun)new SubInt64  ().hashcons(),
    (TypeFun)new MulInt64  ().hashcons(),
    (TypeFun)new NotInt64  ().hashcons()
  };
  
  // Loss-less conversions only
  static TypeFun convert( Type from, Type to ) {
    if( from.isa(TypeInt.INT32) && to.isa(TypeFlt.FLT64) ) return  convInt32Flt64;
    //if( from==Type.UInt32 && to==Type.Int64 ) return convUInt32Int64;
    //if( from==Type.UInt32 && to==Type.FLT64 ) return convUInt32Flt64;
    //if( from==Type. Int64 && to==Type.FLT64 ) return  convInt64Flt64;
    throw AA.unimpl();
  }
}

class PrimPure extends TypeFun {
  PrimPure(String name,String[] args, TypeTuple ts, Type ret) { super(name,args,ts,ret); }
  @Override protected boolean is_pure() { return true; }
  @Override public String toString() { return _name+"::"+_ret; }
}

class ConvertInt32Flt64 extends PrimPure {
  ConvertInt32Flt64() { super("flt64",Prim.ARGS1,TypeTuple.INT32,TypeFlt.FLT64); }
  TypeFlt apply( Type[] args ) { return TypeFlt.make(0,64,(double)args[1].getl()); }
  @Override int op_prec() { return 9; }
  boolean is_lossy() { return false; }
}

//class ConvertUInt32Int64 extends Prim1 {
//  ConvertUInt32Int64() { super(new TypeFun(Type.Int64,Type.UInt32),"__convert"); }
//  ValInt apply( Val[] args ) {  return new ValInt(Type.Int64,args[0].getl()); }
//}
//
//class ConvertUInt32Flt64 extends Prim1 {
//  ConvertUInt32Flt64() { super(new TypeFun(TypeFlt.FLT64,Type.UInt32),"__convert"); }
//  ValFlt apply( Val[] args ) {  return new ValFlt(TypeFlt.FLT64,args[0].getl()); }
//}
//
//class ConvertInt64Flt64 extends Prim1 {
//  ConvertInt64Flt64() { super(new TypeFun(TypeFlt.FLT64,Type.Int64),"__convert"); }
//  ValFlt apply( Val[] args ) {  return new ValFlt(TypeFlt.FLT64,args[0].getl()); }
//}

// 1Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim1OpF64 extends PrimPure {
  Prim1OpF64( String name ) { super(name,Prim.ARGS1,TypeTuple.FLT64,TypeFlt.FLT64); }
  TypeFlt apply( Type[] args ) { return TypeFlt.make(0,64,op(args[1].getd())); }
  abstract double op( double d );
  @Override int op_prec() { return 9; }
}

class MinusFlt64 extends Prim1OpF64 {
  MinusFlt64() { super("-"); }
  double op( double d ) { return -d; }
}

class IDFlt64 extends Prim1OpF64 {
  IDFlt64() { super("id"); }
  double op( double d ) { return d; }
}  

// 1Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim1OpI64 extends PrimPure {
  Prim1OpI64( String name ) { super(name,Prim.ARGS1,TypeTuple.INT64,TypeInt.INT64); }
  TypeInt apply( Type[] args ) { return TypeInt.con(op(args[1].getl())); }
  @Override int op_prec() { return 9; }
  abstract long op( long d );
}

class MinusInt64 extends Prim1OpI64 {
  MinusInt64() { super("-"); }
  long op( long x ) { return -x; }
}

class IDInt64 extends Prim1OpI64 {
  IDInt64() { super("id"); }
  long op( long x ) { return x; }
}  

class NotInt64 extends PrimPure {
  NotInt64() { super("!",Prim.ARGS1,TypeTuple.INT64,TypeInt.BOOL); }
  TypeInt apply( Type[] args ) { return args[1].getl()==0?TypeInt.TRUE:TypeInt.FALSE; }
  @Override int op_prec() { return 9; }
}

// 2Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim2OpF64 extends PrimPure {
  Prim2OpF64( String name ) { super(name,Prim.ARGS2,TypeTuple.FLT64_FLT64,TypeFlt.FLT64); }
  TypeFlt apply( Type[] args ) { return TypeFlt.make(0,64,op(args[1].getd(),args[2].getd())); }
  abstract double op( double x, double y );
}

class AddFlt64 extends Prim2OpF64 {
  AddFlt64() { super("+"); }
  double op( double l, double r ) { return l+r; }
  @Override int op_prec() { return 5; }
}

class SubFlt64 extends Prim2OpF64 {
  SubFlt64() { super("-"); }
  double op( double l, double r ) { return l-r; }
  @Override int op_prec() { return 5; }
}

class MulFlt64 extends Prim2OpF64 {
  MulFlt64() { super("*"); }
  double op( double l, double r ) { return l*r; }
  @Override int op_prec() { return 6; }
}

// 2Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim2OpI64 extends PrimPure {
  Prim2OpI64( String name ) { super(name,Prim.ARGS2,TypeTuple.INT64_INT64,TypeInt.INT64); }
  TypeInt apply( Type[] args ) { return TypeInt.con(op(args[1].getl(),args[2].getl())); }
  abstract long op( long x, long y );
}

class AddInt64 extends Prim2OpI64 {
  AddInt64() { super("+"); }
  long op( long l, long r ) { return l+r; }
  @Override int op_prec() { return 5; }
}

class SubInt64 extends Prim2OpI64 {
  SubInt64() { super("-"); }
  long op( long l, long r ) { return l-r; }
  @Override int op_prec() { return 5; }
}

class MulInt64 extends Prim2OpI64 {
  MulInt64() { super("*"); }
  long op( long l, long r ) { return l*r; }
  @Override int op_prec() { return 6; }
}
