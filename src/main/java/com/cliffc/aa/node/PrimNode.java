package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Primitives can be used as an internal operator (their apply() call does the
// primitive operation).  Primitives are wrapped as functions when returned
// from Env lookup, although the immediate lookup+apply is optimized to just
// make a new primitive.  See FunNode for function Node structure.
//
// Fun/Parm-per-arg/Prim/Ret
//
public abstract class PrimNode extends Node {
  public final String _name;    // Unique name (and program bits)
  final TypeStruct _targs;      // Argument types, 0-based
  final Type _ret;              // Primitive return type, no memory
  Parse _badargs;               // Filled in when inlined in CallNode
  PrimNode( String name, TypeStruct targs, Type ret ) {
    super(OP_PRIM);
    _name=name;
    _targs=targs;
    _ret=ret;
    _badargs=null;
  }

  public static PrimNode[] PRIMS = new PrimNode[] {
    new RandI64(),
    new Id(TypeMemPtr.OOP0), // Pre-split OOP from non-OOP
    new Id(TypeFunPtr.GENERIC_FUNPTR),
    new Id(Type.REAL),

    new ConvertInt64F64(),
    new ConvertStrStr(),

    new MinusF64(),
    new MinusI64(),
    new Not(),

    new   AddF64(),
    new   SubF64(),
    new   MulF64(),

    new   LT_F64(),
    new   LE_F64(),
    new   GT_F64(),
    new   GE_F64(),
    new   EQ_F64(),
    new   NE_F64(),

    new   AddI64(),
    new   SubI64(),
    new   MulI64(),

    new   AndI64(),

    new   LT_I64(),
    new   LE_I64(),
    new   GT_I64(),
    new   GE_I64(),
    new   EQ_I64(),
    new   NE_I64(),

    new   EQ_OOP(),
    new   NE_OOP(),
  };

  public static PrimNode convertTypeName( Type from, Type to, Parse badargs ) {
    return new ConvertTypeName(from,to,badargs);
  }

  // Apply types are 1-based (same as the incoming node index), and not
  // zero-based (not same as the _targs and _args fields).
  public abstract Type apply( Type[] args ); // Execute primitive
  @Override public String xstr() { return _name+"::"+_ret; }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type[] ts = new Type[_defs._len]; // 1-based
    // If the meet with _targs.dual stays above center for all inputs, then we
    // return _ret.dual, the highest allowed result; if all inputs are
    // constants we constant fold; else some input is low so we return _ret,
    // the lowest possible result.
    boolean is_con = true;
    for( int i=1; i<_defs._len; i++ ) { // i=1, skip control
      Type tactual = gvn.type(in(i));
      Type tformal = _targs.at(i-1);
      Type t = tformal.dual().meet(ts[i] = tactual);
      if( t.above_center() ) is_con = false;  // Not a constant
      else if( !t.is_con() ) return _ret;     // Some input is too low
    }
    return is_con ? apply(ts) : _ret.dual();
  }
  @Override public String err(GVNGCM gvn) {
    for( int i=1; i<_defs._len; i++ ) { // i=1, skip control
      Type tactual = gvn.type(in(i));
      Type tformal = _targs.at(i-1);
      if( !tactual.isa(tformal) )
        return _badargs==null ? "bad arguments" : _badargs.typerr(tactual,tformal,null);
    }
    return null;
  }
  // Worse-case type for this Node
  @Override public Type all_type() { return _ret; }
  // Prims are equal for same-name-same-signature (and same inputs).
  // E.g. float-minus of x and y is NOT the same as int-minus of x and y
  // despite both names being '-'.
  @Override public int hashCode() { return super.hashCode()+_name.hashCode()+_targs._hash; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PrimNode) ) return false;
    PrimNode p = (PrimNode)o;
    return _name.equals(p._name) && _targs==p._targs;
  }

  // Called during basic Env creation and making of type constructors, this
  // wraps a PrimNode as a full 1st-class function to be passed about or
  // assigned to variables.
  public FunPtrNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this).add_def(Env.ALL_CTRL)); // Points to ScopeNode only
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    TypeMem tmem = TypeMem.XMEM;
    if( _targs.at(0) instanceof TypeMemPtr ) {
      BitsAlias bas = ((TypeMemPtr)_targs.at(0))._aliases;
      if( bas == BitsAlias.NZERO || bas == BitsAlias.FULL ) tmem = TypeMem.MEM;
      else if( bas == BitsAlias.STRBITS ) tmem = TypeMem.MEM_STR;
      else throw AA.unimpl();
    }
    Node mem = tmem == TypeMem.XMEM ? gvn.con(TypeMem.XMEM)
      : gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(tmem),null));
    add_def(null);              // Control for the primitive in slot 0
    for( int i=0; i<_targs._ts.length; i++ )
      add_def(gvn.init(new ParmNode(i,_targs._flds[i],fun, gvn.con(_targs.at(i)),null)));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mem,gvn.init(this),rpc,fun));
    return new FunPtrNode(ret);
  }


  // --------------------
// Default name constructor using a single tuple type
static class ConvertTypeName extends PrimNode {
  private final Parse _badargs; // Only for converts
  ConvertTypeName(Type from, Type to, Parse badargs) {
    super(to._name,TypeStruct.make(from),to);
    _badargs=badargs;
  }
  @Override public Type value(GVNGCM gvn) {
    Type[] ts = new Type[_defs._len];
    for( int i=1; i<_defs._len; i++ )
      ts[i] = gvn.type(_defs.at(i));
    return apply(ts);     // Apply (convert) even if some args are not constant
  }
  @Override public Type apply( Type[] args ) {
    Type actual = args[1];
    Type formal = _targs.at(0);
    if( formal.dual().isa(actual) && actual.isa(formal) )
      return actual.set_name(_ret._name);
    // If args are illegal, the output is still no worse than _ret in either direction
    return actual.bound(_ret);
  }
  @Override public String err(GVNGCM gvn) {
    Type actual = gvn.type(in(1));
    Type formal = _targs.at(0);
    if( !actual.isa(formal) ) // Actual is not a formal
      return _badargs.typerr(actual,formal,null);
    return null;
  }
}

static class ConvertInt64F64 extends PrimNode {
  ConvertInt64F64() { super("flt64",TypeStruct.INT64,TypeFlt.FLT64); }
  @Override public Type apply( Type[] args ) { return TypeFlt.con((double)args[1].getl()); }
}

  // TODO: Type-check strptr input args
static class ConvertStrStr extends PrimNode {
  ConvertStrStr() { super("str",TypeStruct.STRPTR,TypeMemPtr.STRPTR); }
  @Override public Node ideal(GVNGCM gvn, int level) { return in(1); }
  @Override public Type value(GVNGCM gvn) { return gvn.type(in(1)).bound(_ret); }
  @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
}

// 1Ops have uniform input/output types, so take a shortcut on name printing
abstract static class Prim1OpF64 extends PrimNode {
  Prim1OpF64( String name ) { super(name,TypeStruct.FLT64,TypeFlt.FLT64); }
  public Type apply( Type[] args ) { return TypeFlt.con(op(args[1].getd())); }
  abstract double op( double d );
}

static class MinusF64 extends Prim1OpF64 {
  MinusF64() { super("-"); }
  @Override double op( double d ) { return -d; }
  @Override public byte op_prec() { return 9; }
}

// 1Ops have uniform input/output types, so take a shortcut on name printing
abstract static class Prim1OpI64 extends PrimNode {
  Prim1OpI64( String name ) { super(name,TypeStruct.INT64,TypeInt.INT64); }
  @Override public Type apply( Type[] args ) { return TypeInt.con(op(args[1].getl())); }
  abstract long op( long d );
}

static class MinusI64 extends Prim1OpI64 {
  MinusI64() { super("-"); }
  @Override long op( long x ) { return -x; }
  @Override public byte op_prec() { return 9; }
}

// 2Ops have uniform input/output types, so take a shortcut on name printing
abstract static class Prim2OpF64 extends PrimNode {
  Prim2OpF64( String name ) { super(name,TypeStruct.FLT64_FLT64,TypeFlt.FLT64); }
  @Override public Type apply( Type[] args ) { return TypeFlt.con(op(args[1].getd(),args[2].getd())); }
  abstract double op( double x, double y );
}

static class AddF64 extends Prim2OpF64 {
  AddF64() { super("+"); }
  double op( double l, double r ) { return l+r; }
  @Override public byte op_prec() { return 5; }
}

static class SubF64 extends Prim2OpF64 {
  SubF64() { super("-"); }
  double op( double l, double r ) { return l-r; }
  @Override public byte op_prec() { return 5; }
}

static class MulF64 extends Prim2OpF64 {
  MulF64() { super("*"); }
  @Override double op( double l, double r ) { return l*r; }
  @Override public byte op_prec() { return 6; }
}

// 2RelOps have uniform input types, and bool output
abstract static class Prim2RelOpF64 extends PrimNode {
  Prim2RelOpF64( String name ) { super(name,TypeStruct.FLT64_FLT64,TypeInt.BOOL); }
  @Override public Type apply( Type[] args ) { return op(args[1].getd(),args[2].getd())?TypeInt.TRUE:TypeInt.FALSE; }
  abstract boolean op( double x, double y );
  @Override public byte op_prec() { return 4; }
}

static class LT_F64 extends Prim2RelOpF64 { LT_F64() { super("<" ); } boolean op( double l, double r ) { return l< r; } }
static class LE_F64 extends Prim2RelOpF64 { LE_F64() { super("<="); } boolean op( double l, double r ) { return l<=r; } }
static class GT_F64 extends Prim2RelOpF64 { GT_F64() { super(">" ); } boolean op( double l, double r ) { return l> r; } }
static class GE_F64 extends Prim2RelOpF64 { GE_F64() { super(">="); } boolean op( double l, double r ) { return l>=r; } }
static class EQ_F64 extends Prim2RelOpF64 { EQ_F64() { super("=="); } boolean op( double l, double r ) { return l==r; } }
static class NE_F64 extends Prim2RelOpF64 { NE_F64() { super("!="); } boolean op( double l, double r ) { return l!=r; } }


// 2Ops have uniform input/output types, so take a shortcut on name printing
abstract static class Prim2OpI64 extends PrimNode {
  Prim2OpI64( String name ) { super(name,TypeStruct.INT64_INT64,TypeInt.INT64); }
  @Override public Type apply( Type[] args ) { return TypeInt.con(op(args[1].getl(),args[2].getl())); }
  abstract long op( long x, long y );
}

static class AddI64 extends Prim2OpI64 {
  AddI64() { super("+"); }
  @Override long op( long l, long r ) { return l+r; }
  @Override public byte op_prec() { return 5; }
}

static class SubI64 extends Prim2OpI64 {
  SubI64() { super("-"); }
  @Override long op( long l, long r ) { return l-r; }
  @Override public byte op_prec() { return 5; }
}

static class MulI64 extends Prim2OpI64 {
  MulI64() { super("*"); }
  @Override long op( long l, long r ) { return l*r; }
  @Override public byte op_prec() { return 6; }
}

static class AndI64 extends Prim2OpI64 {
  AndI64() { super("&"); }
  @Override long op( long l, long r ) { return l&r; }
  @Override public byte op_prec() { return 7; }
}

// 2RelOps have uniform input types, and bool output
abstract static class Prim2RelOpI64 extends PrimNode {
  Prim2RelOpI64( String name ) { super(name,TypeStruct.INT64_INT64,TypeInt.BOOL); }
  @Override public Type apply( Type[] args ) { return op(args[1].getl(),args[2].getl())?TypeInt.TRUE:TypeInt.FALSE; }
  abstract boolean op( long x, long y );
  @Override public byte op_prec() { return 4; }
}

static class LT_I64 extends Prim2RelOpI64 { LT_I64() { super("<" ); } boolean op( long l, long r ) { return l< r; } }
static class LE_I64 extends Prim2RelOpI64 { LE_I64() { super("<="); } boolean op( long l, long r ) { return l<=r; } }
static class GT_I64 extends Prim2RelOpI64 { GT_I64() { super(">" ); } boolean op( long l, long r ) { return l> r; } }
static class GE_I64 extends Prim2RelOpI64 { GE_I64() { super(">="); } boolean op( long l, long r ) { return l>=r; } }
static class EQ_I64 extends Prim2RelOpI64 { EQ_I64() { super("=="); } boolean op( long l, long r ) { return l==r; } }
static class NE_I64 extends Prim2RelOpI64 { NE_I64() { super("!="); } boolean op( long l, long r ) { return l!=r; } }


static class EQ_OOP extends PrimNode {
  EQ_OOP() { super("==",TypeStruct.OOP_OOP,TypeInt.BOOL); }
  @Override public Type value(GVNGCM gvn) {
    // Oop-equivalence is based on pointer-equivalence NOT on a "deep equals".
    // Probably need a java-like "===" vs "==" to mean deep-equals.  You are
    // equals if your inputs are the same node, and you are unequals if your
    // input is 2 different NewNodes (or casts of NewNodes).  Otherwise you
    // have to do the runtime test.
    if( in(1)==in(2) ) return TypeInt.TRUE;
    if( in(1) instanceof NewNode &&
        in(2) instanceof NewNode &&
        in(1) != in(2) ) return TypeInt.FALSE;
    // Constants can only do nil-vs-not-nil, since e.g. two strings "abc" and
    // "abc" are equal constants in the type system but can be two different
    // string pointers.
    Type t1 = gvn.type(in(1));
    Type t2 = gvn.type(in(2));
    if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
    if( t1==Type.NIL ) return vs_nil(t2,TypeInt.TRUE,TypeInt.FALSE);
    if( t2==Type.NIL ) return vs_nil(t1,TypeInt.TRUE,TypeInt.FALSE);
    return TypeInt.BOOL;
  }
  @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
  @Override public byte op_prec() { return 4; }
  static Type vs_nil( Type tx, Type t, Type f ) {
    if( tx==Type.NIL ) return t;
    if( tx.above_center() ) return tx.meet_nil()==Type.NIL ? TypeInt.BOOL.dual() : f;
    return tx.must_nil() ? TypeInt.BOOL : f;
  }
}

static class NE_OOP extends PrimNode {
  NE_OOP() { super("!=",TypeStruct.OOP_OOP,TypeInt.BOOL); }
  @Override public Type value(GVNGCM gvn) {
    // Oop-equivalence is based on pointer-equivalence NOT on a "deep equals".
    // Probably need a java-like "===" vs "==" to mean deep-equals.  You are
    // equals if your inputs are the same node, and you are unequals if your
    // input is 2 different NewNodes (or casts of NewNodes).  Otherwise you
    // have to do the runtime test.
    if( in(1)==in(2) ) return TypeInt.FALSE;
    if( in(1) instanceof NewNode &&
        in(2) instanceof NewNode &&
        in(1) != in(2) ) return TypeInt.TRUE;
    // Constants can only do nil-vs-not-nil, since e.g. two strings "abc" and
    // "abc" are equal constants in the type system but can be two different
    // string pointers.
    Type t1 = gvn.type(in(1));
    Type t2 = gvn.type(in(2));
    if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
    if( t1==Type.NIL ) return EQ_OOP.vs_nil(t2,TypeInt.FALSE,TypeInt.TRUE);
    if( t2==Type.NIL ) return EQ_OOP.vs_nil(t1,TypeInt.FALSE,TypeInt.TRUE);
    return TypeInt.BOOL;
  }
  @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
  @Override public byte op_prec() { return 4; }
}


static class Not extends PrimNode {
  // Rare function which takes a Scalar (works for both ints and ptrs)
  Not() { super("!",TypeStruct.SCALAR1,TypeInt.BOOL); }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(1));
    if( t== Type.NIL ) return TypeInt.TRUE;
    if( t. may_nil() ) return TypeInt.BOOL.dual();
    if( t.must_nil() ) return TypeInt.BOOL;
    return TypeInt.FALSE;       // Cannot be a nil
  }
  @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
  @Override public byte op_prec() { return 9; }
}


static class RandI64 extends PrimNode {
  RandI64() { super("math_rand",TypeStruct.INT64,TypeInt.INT64); }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(1));
    if( t.above_center() ) return TypeInt.BOOL.dual();
    return t.meet(TypeInt.FALSE).bound(TypeInt.INT64);
  }
  @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
  // Rands have hidden internal state; 2 Rands are never equal
  @Override public boolean equals(Object o) { return this==o; }
}

static class Id extends PrimNode {
  Id(Type arg) { super("id",TypeStruct.make(arg),arg); }
  @Override public Node ideal(GVNGCM gvn, int level) { return in(1); }
  @Override public Type value(GVNGCM gvn) { return gvn.type(in(1)).bound(_ret); }
  @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
}

}
