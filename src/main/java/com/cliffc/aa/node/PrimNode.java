package com.cliffc.aa.node;

import com.cliffc.aa.*;


// Primitives can be used as an internal operator (their apply() call does the
// primitive operation).  Primitives are wrapped as functions when returned
// from Env lookup, although the immediate lookup+apply is optimized to just
// make a new primitive.  See FunNode for function Node structure.
//
// Fun/Parm-per-arg/Prim/Ret
//

public abstract class PrimNode extends Node {
  public final TypeFun _tf;
  public final String _name;    // Unique name (and program bits)
  public final String[] _args;  // Handy
  PrimNode( String name, String[] args, TypeFun tf, Node... nodes ) { super(OP_PRIM,nodes); _name=name; _args=args; _tf = tf; }
  
  final static String[] ARGS0 = new String[]{};
  final static String[] ARGS1 = new String[]{"x"};
  final static String[] ARGS2 = new String[]{"x","y"};

  public static PrimNode[] PRIMS = new PrimNode[] {
    new    RandI64(),
    new    Id(),
    
    new ConvertInt32Flt64(),

    new MinusFlt64(),
    new MinusInt64(),
    new   NotInt64(),

    new   AddFlt64(),
    new   SubFlt64(),
    new   MulFlt64(),
          
    new   AddInt64(),
    new   SubInt64(),
    new   MulInt64(),

  };

  // Loss-less conversions only
  static PrimNode convert( Node actual, Type from, Type to ) {
    if( from.isa(TypeInt.INT32) && to.isa(TypeFlt.FLT64) ) return new ConvertInt32Flt64(null,actual);
    //if( from==Type.UInt32 && to==Type.Int64 ) return convUInt32Int64;
    //if( from==Type.UInt32 && to==Type.FLT64 ) return convUInt32Flt64;
    //if( from==Type. Int64 && to==Type.FLT64 ) return  convInt64Flt64;
    throw AA.unimpl();
  }
  
  public abstract Type apply( Type[] args ); // Execute primitive
  public boolean is_lossy() { return true; }
  @Override public String str() { return _name+"::"+_tf._ret; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type[] ts = new Type[_defs._len];
    boolean con=true;
    for( int i=1; i<_defs._len; i++ ) {
      ts[i] = gvn.type(_defs.at(i));
      if( ts[i] instanceof TypeErr ) return ts[i]; // Errors poison
      if( !ts[i].is_con() ) { con=false; break; }
    }
    return con ? apply(ts) : _tf._ret;
  }
}

class ConvertInt32Flt64 extends PrimNode {
  ConvertInt32Flt64(Node... nodes) { super("flt64",PrimNode.ARGS1,TypeFun.make(TypeTuple.INT32,TypeFlt.FLT64),nodes); }
  @Override public TypeFlt apply( Type[] args ) { return TypeFlt.make(0,64,(double)args[1].getl()); }
  @Override public int op_prec() { return 9; }
  public boolean is_lossy() { return false; }
}

// 1Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim1OpF64 extends PrimNode {
  Prim1OpF64( String name ) { super(name,PrimNode.ARGS1,TypeFun.FLT64); }
  public TypeFlt apply( Type[] args ) { return TypeFlt.make(0,64,op(args[1].getd())); }
  abstract double op( double d );
  @Override public int op_prec() { return 9; }
}

class MinusFlt64 extends Prim1OpF64 {
  MinusFlt64() { super("-"); }
  double op( double d ) { return -d; }
}

// 1Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim1OpI64 extends PrimNode {
  Prim1OpI64( String name ) { super(name,PrimNode.ARGS1,TypeFun.INT64); }
  public TypeInt apply( Type[] args ) { return TypeInt.con(op(args[1].getl())); }
  @Override public int op_prec() { return 9; }
  abstract long op( long d );
}

class MinusInt64 extends Prim1OpI64 {
  MinusInt64() { super("-"); }
  long op( long x ) { return -x; }
}

class NotInt64 extends PrimNode {
  NotInt64() { super("!",PrimNode.ARGS1,TypeFun.make(TypeTuple.INT64,TypeInt.BOOL)); }
  public TypeInt apply( Type[] args ) { return args[1].getl()==0?TypeInt.TRUE:TypeInt.FALSE; }
  @Override public int op_prec() { return 9; }
}

// 2Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim2OpF64 extends PrimNode {
  Prim2OpF64( String name ) { super(name,PrimNode.ARGS2,TypeFun.FLT64_FLT64); }
  public TypeFlt apply( Type[] args ) { return TypeFlt.make(0,64,op(args[1].getd(),args[2].getd())); }
  abstract double op( double x, double y );
}

class AddFlt64 extends Prim2OpF64 {
  AddFlt64() { super("+"); }
  double op( double l, double r ) { return l+r; }
  @Override public int op_prec() { return 5; }
}

class SubFlt64 extends Prim2OpF64 {
  SubFlt64() { super("-"); }
  double op( double l, double r ) { return l-r; }
  @Override public int op_prec() { return 5; }
}

class MulFlt64 extends Prim2OpF64 {
  MulFlt64() { super("*"); }
  double op( double l, double r ) { return l*r; }
  @Override public int op_prec() { return 6; }
}

// 2Ops have uniform input/output types, so take a shortcut on name printing
abstract class Prim2OpI64 extends PrimNode {
  Prim2OpI64( String name ) { super(name,PrimNode.ARGS2,TypeFun.INT64_INT64); }
  public TypeInt apply( Type[] args ) { return TypeInt.con(op(args[1].getl(),args[2].getl())); }
  abstract long op( long x, long y );
}

class AddInt64 extends Prim2OpI64 {
  AddInt64() { super("+"); }
  long op( long l, long r ) { return l+r; }
  @Override public int op_prec() { return 5; }
}

class SubInt64 extends Prim2OpI64 {
  SubInt64() { super("-"); }
  long op( long l, long r ) { return l-r; }
  @Override public int op_prec() { return 5; }
}

class MulInt64 extends Prim2OpI64 {
  MulInt64() { super("*"); }
  long op( long l, long r ) { return l*r; }
  @Override public int op_prec() { return 6; }
}

class RandI64 extends PrimNode {
  RandI64() { super("math_rand",PrimNode.ARGS1,TypeFun.INT64_INT64); }
  @Override public TypeInt apply( Type[] args ) { return TypeInt.con(new java.util.Random().nextInt((int)args[1].getl())); }
  @Override public Type value(GVNGCM gvn) { return TypeInt.INT64; }
}

class Id extends PrimNode {
  Id() { super("id",PrimNode.ARGS1,TypeFun.SCR1); }
  @Override public Type apply( Type[] args ) { return args[1]; }
  @Override public Node ideal(GVNGCM gvn) { return at(1); }
  @Override public Type value(GVNGCM gvn) { return gvn.type(at(1)); }
}

