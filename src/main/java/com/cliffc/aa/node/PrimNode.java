package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;
import static com.cliffc.aa.type.TypeStruct.CANONICAL_INSTANCE;

// Primitives are nodes to do primitive operations.  Internally they carry a
// '_formals' to type their arguments.  Similar to functions and FunNodes and
// unlike structs and NewNodes, the arguments are ordered.  The inputs to
// the Node itself and the formals are numbered.  Example:
// - index CTL_IDX, typically null
// - index MEM_IDX, typically null except for e.g. Load/Store primitives
// - index DSP_IDX, typically the left arg, NOT the Display nor 'self'
// - index ARG_IDX, typically the right arg

// Primitives use their apply() call as the transfer function and expect the
// args in this order.

// Primitives are wrapped as functions when returned from Env lookup, although
// the immediate lookup+apply is optimized to just make a new primitive.  See
// FunNode for function Node structure.  The wrapping function preserves the
// order in the ParmNodes.

// Both 'int' and 'flt' are clazzes, refer to internal Structs and containing
// fields for each of the primitive operator function wrappers.  The normal
// primitives are wrapped in a named Struct with a single field 'x', and the
// Field lookup node checks the clazz after looking in the wrapper.

public abstract class PrimNode extends Node {
  public final String _name;    // Unique name (and program bits)
  public final TypeFunPtr _tfp; // FIDX, nargs, display argument, WRAPPED primitive return type
  public final TypeTuple _formals; // Formals are indexed by order NOT name and are wrapped prims.
  public final Type _ret;       // Wrapped primitive return
  public final boolean _is_lazy;// 2nd arg is lazy (thunked by parser)
  Parse[] _badargs;             // Filled in when inlined in CallNode
  public PrimNode( String name, TypeTuple formals, Type ret ) { this(name,false,formals,ret); }
  public PrimNode( String name, boolean is_lazy, TypeTuple formals, Type ret ) {
    super(OP_PRIM);
    _name = name;
    _is_lazy = is_lazy;
    int fidx = BitsFun.new_fidx();
    _formals = formals;
    _ret = ret;
    _tfp=TypeFunPtr.make(BitsFun.make0(fidx),formals.len(),TypeMemPtr.NO_DISP,ret);
    _badargs=null;
  }

  private static PrimNode[] PRIMS = null; // All primitives

  public static PrimNode[] PRIMS() {
    if( PRIMS!=null ) return PRIMS;

    // int opers
    PrimNode[] INTS = new PrimNode[]{
      new MinusI64(), new NotI64(),
      new MulI64 (), new DivI64 (), new MulIF64(), new DivIF64(), new ModI64(),
      new AddI64 (), new SubI64 (), new AddIF64(), new SubIF64(),
      new LT_I64 (), new LE_I64 (), new GT_I64 (), new GE_I64 (),
      new LT_IF64(), new LE_IF64(), new GT_IF64(), new GE_IF64(),
      new EQ_I64 (), new NE_I64 (),
      new EQ_IF64(), new NE_IF64(),
      new AndI64 (), new AndThen(),
      new OrI64  (), new OrElse(),
    };

    PrimNode[] FLTS = new PrimNode[]{
      new MinusF64(),
      new MulF64 (), new DivF64 (), new MulFI64(), new DivFI64(),
      new AddF64 (), new SubF64 (), new AddFI64(), new SubFI64(),
      new LT_F64 (), new LE_F64 (), new GT_F64 (), new GE_F64 (),
      new LT_FI64(), new LE_FI64(), new GT_FI64(), new GE_FI64(),
      new EQ_F64 (), new NE_F64 (),
      new EQ_FI64(), new NE_FI64()
    };
    // Other primitives, not binary operators
    PrimNode rand = new RandI64();
    PrimNode[] others = new PrimNode[] {
      // These are called like a function, so do not have a precedence
      rand,
      new ConvertI64F64(),

      //new EQ_OOP(), new NE_OOP(), new Not(),
      //// These are balanced-ops, called by Parse.term()
      //new MemPrimNode.ReadPrimNode.LValueRead  (), // Read  an L-Value: (ary,idx) ==> elem
      //new MemPrimNode.ReadPrimNode.LValueWrite (), // Write an L-Value: (ary,idx,elem) ==> elem
      //new MemPrimNode.ReadPrimNode.LValueWriteFinal(), // Final Write an L-Value: (ary,idx,elem) ==> elem

      // These are unary ops, precedence determined outside 'Parse.expr'
      //new MemPrimNode.ReadPrimNode.LValueLength(), // The other array ops are "balanced ops" and use term() for precedence
    };

    // Gather
    Ary<PrimNode> allprims = new Ary<>(others);
    for( PrimNode prim : others ) allprims.push(prim);
    for( PrimNode prim : INTS   ) allprims.push(prim);
    for( PrimNode prim : FLTS   ) allprims.push(prim);
    PRIMS = allprims.asAry();

    // Build the int and float types and prototypes
    install("int",INTS,TypeStruct.INT);
    install("flt",FLTS,TypeStruct.FLT);

    // Math package
    install_math(rand);

    return PRIMS;
  }

  public static TypeStruct make_int(long   i) { return TypeStruct.make_int(TypeInt.con(i)); }
  public static TypeStruct make_flt(double d) { return TypeStruct.make_flt(TypeFlt.con(d)); }

  public static TypeStruct make_wrap(Type t) {
    return TypeStruct.make(t instanceof TypeInt ? "int:" : "flt:",t);
  }
  public static TypeInt unwrap_i(Type t) { return (TypeInt)((TypeStruct)t)._def; }
  public static TypeFlt unwrap_f(Type t) { return (TypeFlt)((TypeStruct)t)._def; }
  public static long   unwrap_ii(Type t) { return t==TypeNil.XNIL ? 0 : unwrap_i(t).getl(); }
  public static double unwrap_ff(Type t) { return unwrap_f(t).getd(); }

  // Make and install a primitive Clazz.
  private static void install( String s, PrimNode[] prims, TypeStruct canonical_prim ) {
    String tname = (s+":").intern();
    StructNode rec = new StructNode(false,false,null);
    for( PrimNode prim : prims ) prim.as_fun(rec,true);
    for( Node n : rec._defs )
      if( n instanceof UnresolvedNode unr )
        Env.GVN.add_work_new(unr.define()); // Flag all overloaded prims as being known
    rec.add_fld(TypeFld.make(CANONICAL_INSTANCE,canonical_prim),Node.con(canonical_prim),null);
    rec.init();
    rec.close();
    Env.PROTOS.put(s,rec);         // clazz String -> clazz Struct mapping, for values
    Env.SCP_0.add_type(tname,rec); // type  String -> clazz Struct mapping, for types
    // Inject the primitive class into scope above top-level display
    alloc_inject(rec,s);
  }

  // Primitive wrapped as a simple function.
  // Fun Parm_dsp [Parm_y] prim Ret
  // No memory, no RPC.  Display is first arg.
  private void as_fun( StructNode rec, boolean is_oper ) {
    String op = is_oper ? (switch( _tfp.nargs() ) {
      case ARG_IDX+1 -> "_";
      case ARG_IDX   -> "";
      default -> throw unimpl();
      }+_name+"_").intern() : _name;
    if( is_oper ) Oper.make(op,_is_lazy);

    FunNode fun = new FunNode(this,is_oper ? op : _name);
    fun.add_def(new CRProjNode(fun._fidx).init()); // Need FIDX to make the default control
    fun.init();                 // Now register with parser
    if( _is_lazy ) add_def(fun); // Ctrl in slot 0
    ParmNode rpc = new ParmNode(0,fun,null,TypeRPC.ALL_CALL,Env.ALL_CALL).init();
    for( int i=_is_lazy ? MEM_IDX : DSP_IDX; i<_formals.len(); i++ ) {
      // Make a Parm for every formal
      Type tformal = _formals.at(i);
      Node nformal;
      if(      tformal==TypeStruct.INT ) nformal = Env.INT;
      else if( tformal==TypeStruct.FLT ) nformal = Env.FLT;
      else if( tformal==Type.ALL       ) nformal = Env.ALL;
      else if( tformal==TypeFunPtr.THUNK)nformal = Env.THUNK;
      else if( tformal==TypeMem.ALLMEM ) nformal = Env.ALLMEM;
      else throw unimpl();
      add_def(new ParmNode(i,fun,null,tformal,nformal).init());
    }
    // The primitive, working on and producing wrapped prims
    init();
    // If lazy, need control and memory results
    Node zctrl = _is_lazy ? new CProjNode(this).init() : fun;
    Node zmem  = _is_lazy ? new MProjNode(this).init() : null;
    Node zrez  = _is_lazy ? new  ProjNode(this,REZ_IDX).init() : this;
    // Return the result
    RetNode ret = new RetNode(zctrl,zmem,zrez,rpc,fun).init();
    // FunPtr is UNBOUND here, will be bound when loaded thru a named struct to the Clazz.
    FunPtrNode fptr = new FunPtrNode(op,ret,Env.ALL).init();
    rec.add_fun(op,Access.Final,fptr,null);
  }

  // Build and install match package
  private static void install_math(PrimNode rand) {
    StructNode rec = new StructNode(false,false,null);
    rand.as_fun(rec,false);
    Type pi = make_wrap(TypeFlt.PI);
    rec.add_fld(TypeFld.make("pi",pi),Node.con(pi),null);
    rec.close();
    Env.GVN.init(rec);
    alloc_inject(rec,"math");
  }

  // Allocate and inject above top display
  private static void alloc_inject(StructNode rec, String name) {
    // Inject the primitive class above top-level display
    Node mem = Env.SCP_0.mem();
    NewNode dsp = (NewNode)mem.in(0);
    NewNode nnn = new NewNode(dsp.mem(),rec).init(); // Allocate primitive clazz; they have memory
    dsp.set_def(MEM_IDX,new MProjNode(nnn).init());
    Node ptr = new ProjNode(nnn,REZ_IDX).init();
    Env.STK_0.add_fld(TypeFld.make(name,ptr._val),ptr,null);
    dsp.xval();
    mem.xval();
  }


  // Apply uses the same alignment as the arguments, ParmNodes, _formals.
  public abstract Type apply( Type[] args ); // Execute primitive
  // Pretty print short primitive signature based on first argument:
  //  + :{int int -> int }  ==>>   + :int
  //  + :{flt flt -> flt }  ==>>   + :flt
  //  + :{str str -> str }  ==>>   + :str
  // str:{int     -> str }  ==>>  str:int
  // str:{flt     -> str }  ==>>  str:flt
  // == :{ptr ptr -> int1}  ==>>  == :ptr
  @Override public String xstr() { return _name+":"+_formals.at(DSP_IDX); }
  private static final Type[] TS = new Type[ARG_IDX+1];
  @Override public Type value() {
    if( is_keep() ) return _val;
    // If all inputs are constants we constant-fold.  If any input is high, we
    // return high otherwise we return low.
    boolean is_con = true, has_high = false;
    for( int i=DSP_IDX; i<_formals.len(); i++ ) {
      Type tactual = TS[i-DSP_IDX] = val(i-DSP_IDX);
      Type tformal = _formals.at(i);
      Type t = tformal.dual().meet(tactual);
      if( tactual != TypeNil.XNIL && !t.is_con() ) {
        is_con = false;         // Some non-constant
        if( t.above_center() ) has_high=true;
      }
    }
    return is_con ? apply(TS) : (has_high ? _ret.dual() : _ret);
  }

  @Override public boolean has_tvar() { return true; }

  // In the test HM, All primitives are effectively H-M Applies with a hidden
  // internal Lambda.  Here there is already a wrapper Lambda, and the
  // primitive computes a result.
  @Override public boolean unify( boolean test ) {
    TV2 self = tvar();
    if( self.is_base() && !self.is_copy() ) return false;
    // TODO: unify self with _tfp._ret base
    // TODO: unify input args to formals
    return test || self.unify(TV2.make_base(_tfp._ret,"PrimNode_create").clr_cp(),test);
  }

  @Override public ErrMsg err( boolean fast ) {
    for( int i=DSP_IDX; i<_formals.len(); i++ ) {
      Type tactual = val(i-DSP_IDX);
      Type tformal = _formals.at(i);
      if( !tactual.isa(tformal) )
        return _badargs==null ? ErrMsg.BADARGS : ErrMsg.typerr(_badargs[i],tactual, tformal);
    }
    return null;
  }
  // Prims are equal for same-name-same-signature (and same inputs).
  // E.g. float-minus of x and y is NOT the same as int-minus of x and y
  // despite both names being '-'.
  @Override public int hashCode() { return super.hashCode()+_name.hashCode()+(int)_formals._hash; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PrimNode p) ) return false;
    return Util.eq(_name,p._name) && _formals==p._formals;
  }

  public static class ConvertI64F64 extends PrimNode {
    public ConvertI64F64() { super("flt",TypeTuple.INT64,TypeStruct.FLT); }
    @Override public Type apply( Type[] args ) { return make_flt((double)unwrap_ii(args[0])); }
  }

  // 1Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim1OpF64 extends PrimNode {
    Prim1OpF64( String name ) { super(name,TypeTuple.FLT64,TypeStruct.FLT); }
    public Type apply( Type[] args ) { return make_flt(op(unwrap_ff(args[0]))); }
    abstract double op( double d );
  }

  static class MinusF64 extends Prim1OpF64 { MinusF64() { super("-"); } double op( double d ) { return -d; } }

  // 1Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim1OpI64 extends PrimNode {
    Prim1OpI64( String name ) { super(name,TypeTuple.INT64,TypeStruct.INT); }
    @Override public Type apply( Type[] args ) { return make_int(op(unwrap_ii(args[0]))); }
    abstract long op( long d );
  }

  static class MinusI64 extends Prim1OpI64 { MinusI64() { super("-"); } long op( long x ) { return -x; } }
  static class NotI64 extends PrimNode {
    // Rare function which takes a Scalar (works for both ints and ptrs).
    public NotI64() { super("!",TypeTuple.INT64,TypeStruct.BOOL); }
    @Override public Type value() {
      Type t0 = val(0);
      if( t0==Type.ANY ) return TypeStruct.BOOL.dual();
      if( t0 == TypeNil.NIL || t0 == TypeNil.XNIL )
        return make_int(1);     // !nil is 1
      if( t0==Type.ALL ) return TypeStruct.BOOL;
      TypeInt t1 = unwrap_i(t0);
      if( t1._nil ) {
        return t1._sub ? TypeStruct.BOOL.dual() : make_int(1);
      } else {
        return t1._sub ? TypeNil.XNIL : TypeStruct.BOOL;
      }
    }
    @Override public Type apply( Type[] args ) { throw AA.unimpl(); }
  }


  // 2Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim2OpF64 extends PrimNode {
    Prim2OpF64( String name ) { super(name,TypeTuple.FLT64_FLT64,TypeStruct.FLT); }
    @Override public Type apply( Type[] args ) { return make_flt(op(unwrap_ff(args[0]),unwrap_ff(args[1]))); }
    abstract double op( double x, double y );
  }

  static class AddF64 extends Prim2OpF64 { AddF64() { super("+"); } double op( double l, double r ) { return l+r; } }
  static class SubF64 extends Prim2OpF64 { SubF64() { super("-"); } double op( double l, double r ) { return l-r; } }
  static class MulF64 extends Prim2OpF64 { MulF64() { super("*"); } double op( double l, double r ) { return l*r; } }
  static class DivF64 extends Prim2OpF64 { DivF64() { super("/"); } double op( double l, double r ) { return l/r; } }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpF64 extends PrimNode {
    Prim2RelOpF64( String name ) { super(name,TypeTuple.FLT64_FLT64,TypeStruct.BOOL); }
    @Override public Type apply( Type[] args ) { return op(unwrap_ff(args[0]),unwrap_ff(args[1]))?make_int(1):TypeNil.XNIL; }
    abstract boolean op( double x, double y );
  }

  public static class LT_F64 extends Prim2RelOpF64 { public LT_F64() { super("<" ); } boolean op( double l, double r ) { return l< r; } }
  public static class LE_F64 extends Prim2RelOpF64 { public LE_F64() { super("<="); } boolean op( double l, double r ) { return l<=r; } }
  public static class GT_F64 extends Prim2RelOpF64 { public GT_F64() { super(">" ); } boolean op( double l, double r ) { return l> r; } }
  public static class GE_F64 extends Prim2RelOpF64 { public GE_F64() { super(">="); } boolean op( double l, double r ) { return l>=r; } }
  public static class EQ_F64 extends Prim2RelOpF64 { public EQ_F64() { super("=="); } boolean op( double l, double r ) { return l==r; } }
  public static class NE_F64 extends Prim2RelOpF64 { public NE_F64() { super("!="); } boolean op( double l, double r ) { return l!=r; } }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpFI64 extends PrimNode {
    Prim2RelOpFI64( String name ) { super(name,TypeTuple.FLT64_INT64,TypeStruct.BOOL); }
    @Override public Type apply( Type[] args ) { return op(unwrap_ff(args[0]),unwrap_ii(args[1]))?make_int(1):TypeNil.XNIL; }
    abstract boolean op( double x, long y );
  }

  public static class LT_FI64 extends Prim2RelOpFI64 { public LT_FI64() { super("<" ); } boolean op( double l, long r ) { return l< r; } }
  public static class LE_FI64 extends Prim2RelOpFI64 { public LE_FI64() { super("<="); } boolean op( double l, long r ) { return l<=r; } }
  public static class GT_FI64 extends Prim2RelOpFI64 { public GT_FI64() { super(">" ); } boolean op( double l, long r ) { return l> r; } }
  public static class GE_FI64 extends Prim2RelOpFI64 { public GE_FI64() { super(">="); } boolean op( double l, long r ) { return l>=r; } }
  public static class EQ_FI64 extends Prim2RelOpFI64 { public EQ_FI64() { super("=="); } boolean op( double l, long r ) { return l==r; } }
  public static class NE_FI64 extends Prim2RelOpFI64 { public NE_FI64() { super("!="); } boolean op( double l, long r ) { return l!=r; } }


  // 2Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim2OpI64 extends PrimNode {
    Prim2OpI64( String name ) { super(name,TypeTuple.INT64_INT64,TypeStruct.INT); }
    @Override public Type apply( Type[] args ) { return make_int(op(unwrap_ii(args[0]),unwrap_ii(args[1]))); }
    abstract long op( long x, long y );
  }

  static class AddI64 extends Prim2OpI64 { AddI64() { super("+"); } long op( long l, long r ) { return l+r; } }
  static class SubI64 extends Prim2OpI64 { SubI64() { super("-"); } long op( long l, long r ) { return l-r; } }
  static class MulI64 extends Prim2OpI64 { MulI64() { super("*"); } long op( long l, long r ) { return l*r; } }
  static class DivI64 extends Prim2OpI64 { DivI64() { super("/"); } long op( long l, long r ) { return r==0 ? 0 : l/r; } } // Long division
  static class ModI64 extends Prim2OpI64 { ModI64() { super("%"); } long op( long l, long r ) { return r==0 ? 0 : l%r; } }

  abstract static class Prim2OpIF64 extends PrimNode {
    Prim2OpIF64( String name ) { super(name,TypeTuple.INT64_FLT64,TypeStruct.FLT); }
    @Override public Type apply( Type[] args ) { return make_flt(op(unwrap_ii(args[0]),unwrap_ff(args[1]))); }
    abstract double op( long x, double y );
  }
  static class AddIF64 extends Prim2OpIF64 { AddIF64() { super("+"); } double op( long l, double r ) { return l+r; } }
  static class SubIF64 extends Prim2OpIF64 { SubIF64() { super("-"); } double op( long l, double r ) { return l-r; } }
  static class MulIF64 extends Prim2OpIF64 { MulIF64() { super("*"); } double op( long l, double r ) { return l*r; } }
  static class DivIF64 extends Prim2OpIF64 { DivIF64() { super("/"); } double op( long l, double r ) { return l/r; } } // Float division, by 0 gives infinity

  abstract static class Prim2OpFI64 extends PrimNode {
    Prim2OpFI64( String name ) { super(name,TypeTuple.FLT64_INT64,TypeStruct.FLT); }
    @Override public Type apply( Type[] args ) { return make_flt(op(unwrap_ff(args[0]),unwrap_ii(args[1]))); }
    abstract double op( double x, long y );
  }
  static class AddFI64 extends Prim2OpFI64 { AddFI64() { super("+"); } double op( double l, long r ) { return l+r; } }
  static class SubFI64 extends Prim2OpFI64 { SubFI64() { super("-"); } double op( double l, long r ) { return l-r; } }
  static class MulFI64 extends Prim2OpFI64 { MulFI64() { super("*"); } double op( double l, long r ) { return l*r; } }
  static class DivFI64 extends Prim2OpFI64 { DivFI64() { super("/"); } double op( double l, long r ) { return l/r; } } // Float division, by 0 gives infinity

  public static class AndI64 extends Prim2OpI64 {
    public AndI64() { super("&"); }
    // And can preserve bit-width
    @Override public Type value() {
      Type t0 = val(0), t1 = val(1);
      if( t0==Type.ANY || t1==Type.ANY ) return TypeStruct.INT.dual();
      if( t0==Type.ALL || t1==Type.ALL ) return TypeStruct.INT;
      // 0 AND anything is 0
      if( t0 == TypeNil.XNIL || t1 == TypeNil.XNIL ) return TypeNil.XNIL;
      // If either is high - results might fall to something reasonable
      t0 = unwrap_i(t0);
      t1 = unwrap_i(t1);
      if( t0.above_center() || t1.above_center() )
        return TypeStruct.INT.dual();
      // Both are low-or-constant, and one is not valid - return bottom result
      if( !t0.isa(TypeInt.INT64) || !t1.isa(TypeInt.INT64) )
        return TypeStruct.INT;
      // If both are constant ints, return the constant math.
      if( t0.is_con() && t1.is_con() ) {
        long i2 = t0.getl() & t1.getl();
        return i2==0 ? TypeNil.XNIL : make_int(i2);
      }
      //if( !(t0 instanceof TypeInt) || !(t1 instanceof TypeInt) )
      //  return TypeStruct.INT;
      // Preserve width
      return make_wrap(((TypeInt)t0).minsize((TypeInt)t1));
    }
    @Override long op( long l, long r ) { return l&r; }
  }

  public static class OrI64 extends Prim2OpI64 {
    public OrI64() { super("|"); }
    // And can preserve bit-width
    @Override public Type value() {
      if( is_keep() ) return _val;
      Type t0 = val(0), t1 = val(1);
      if( t0==Type.ANY || t1==Type.ANY ) return TypeStruct.INT.dual();
      if( t0==Type.ALL || t1==Type.ALL ) return TypeStruct.INT;
      // 0 OR anything is that thing
      if( t0 == TypeNil.XNIL ) return t1;
      if( t1 == TypeNil.XNIL ) return t0;
      t0 = unwrap_i(t0);
      t1 = unwrap_i(t1);
      // If either is high - results might fall to something reasonable
      if( t0.above_center() || t1.above_center() )
        return TypeStruct.INT.dual();
      // Both are low-or-constant, and one is not valid - return bottom result
      if( !t0.isa(TypeInt.INT64) || !t1.isa(TypeInt.INT64) )
        return TypeStruct.INT;
      // If both are constant ints, return the constant math.
      if( t0.is_con() && t1.is_con() )
        return make_int(t0.getl() | t1.getl());
      //if( !(t0 instanceof TypeInt) || !(t1 instanceof TypeInt) )
      //  return TypeInt.INT64;
      // Preserve width
      return make_wrap(((TypeInt)t0).maxsize((TypeInt)t1));
    }
    @Override long op( long l, long r ) { return l&r; }
  }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpI64 extends PrimNode {
    Prim2RelOpI64( String name ) { super(name,TypeTuple.INT64_INT64,TypeStruct.BOOL); }
    @Override public Type apply( Type[] args ) {
      return op(unwrap_ii(args[0]),unwrap_ii(args[1]))?make_int(1):TypeNil.XNIL;
    }
    abstract boolean op( long x, long y );
  }

  public static class LT_I64 extends Prim2RelOpI64 { public LT_I64() { super("<" ); } boolean op( long l, long r ) { return l< r; } }
  public static class LE_I64 extends Prim2RelOpI64 { public LE_I64() { super("<="); } boolean op( long l, long r ) { return l<=r; } }
  public static class GT_I64 extends Prim2RelOpI64 { public GT_I64() { super(">" ); } boolean op( long l, long r ) { return l> r; } }
  public static class GE_I64 extends Prim2RelOpI64 { public GE_I64() { super(">="); } boolean op( long l, long r ) { return l>=r; } }
  public static class EQ_I64 extends Prim2RelOpI64 { public EQ_I64() { super("=="); } boolean op( long l, long r ) { return l==r; } }
  public static class NE_I64 extends Prim2RelOpI64 { public NE_I64() { super("!="); } boolean op( long l, long r ) { return l!=r; } }

  abstract static class Prim2RelOpIF64 extends PrimNode {
    Prim2RelOpIF64( String name ) { super(name,TypeTuple.INT64_FLT64,TypeStruct.BOOL); }
    @Override public Type apply( Type[] args ) { return op(unwrap_ii(args[0]),unwrap_ff(args[1]))?make_int(1):TypeNil.XNIL; }
    abstract boolean op( long x, double y );
  }

  public static class LT_IF64 extends Prim2RelOpIF64 { public LT_IF64() { super("<" ); } boolean op( long l, double r ) { return l< r; } }
  public static class LE_IF64 extends Prim2RelOpIF64 { public LE_IF64() { super("<="); } boolean op( long l, double r ) { return l<=r; } }
  public static class GT_IF64 extends Prim2RelOpIF64 { public GT_IF64() { super(">" ); } boolean op( long l, double r ) { return l> r; } }
  public static class GE_IF64 extends Prim2RelOpIF64 { public GE_IF64() { super(">="); } boolean op( long l, double r ) { return l>=r; } }
  public static class EQ_IF64 extends Prim2RelOpIF64 { public EQ_IF64() { super("=="); } boolean op( long l, double r ) { return l==r; } }
  public static class NE_IF64 extends Prim2RelOpIF64 { public NE_IF64() { super("!="); } boolean op( long l, double r ) { return l!=r; } }


  public static class EQ_OOP extends PrimNode {
    public EQ_OOP() { super("==",TypeTuple.OOP_OOP,TypeInt.BOOL); }
    @Override public Type value() {
      if( is_keep() ) return _val;
      //// Oop-equivalence is based on pointer-equivalence NOT on a "deep equals".
      //// Probably need a java-like "eq" vs "==" to mean deep-equals.  You are
      //// equals if your inputs are the same node, and you are unequals if your
      //// input is 2 different NewNodes (or casts of NewNodes).  Otherwise, you
      //// have to do the runtime test.
      //Node in1 = in(0), in2 = in(1);
      //if( in1==in2 ) return TypeInt.TRUE;
      //Node nn1 = in1.in(0), nn2 = in2.in(0);
      //if( nn1 instanceof NewNode &&
      //    nn2 instanceof NewNode &&
      //    nn1 != nn2 ) return TypeInt.FALSE;
      //// Constants can only do nil-vs-not-nil, since e.g. two strings "abc" and
      //// "abc" are equal constants in the type system but can be two different
      //// string pointers.
      //Type t1 = in1._val;
      //Type t2 = in2._val;
      //if( t1==Type.NIL || t1==Type.XNIL ) return vs_nil(t2,TypeInt.TRUE,TypeInt.FALSE);
      //if( t2==Type.NIL || t2==Type.XNIL ) return vs_nil(t1,TypeInt.TRUE,TypeInt.FALSE);
      //if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
      //return TypeInt.BOOL;
      throw unimpl();
    }
    @Override public Type apply( Type[] args ) { throw AA.unimpl(); }
    static Type vs_nil( Type tx, Type t, Type f ) {
      if( tx==TypeNil.XNIL ) return t;
      //if( tx.above_center() ) return tx.isa(TypeNil.XNIL) ? TypeInt.BOOL.dual() : f;
      //return tx.must_nil() ? TypeInt.BOOL : f;
      throw unimpl();
    }
  }

  public static class NE_OOP extends PrimNode {
    public NE_OOP() { super("!=",TypeTuple.OOP_OOP,TypeInt.BOOL); }
    @Override public Type value() {
      if( is_keep() ) return _val;
      //// Oop-equivalence is based on pointer-equivalence NOT on a "deep equals".
      //// Probably need a java-like "===" vs "==" to mean deep-equals.  You are
      //// equals if your inputs are the same node, and you are unequals if your
      //// input is 2 different NewNodes (or casts of NewNodes).  Otherwise, you
      //// have to do the runtime test.
      //Node in1 = in(0), in2 = in(1);
      //if( in1==in2 ) return TypeInt.FALSE;
      //Node nn1 = in1.in(0), nn2 = in2.in(0);
      //if( nn1 instanceof NewNode &&
      //    nn2 instanceof NewNode &&
      //    nn1 != nn2 ) return TypeInt.TRUE;
      //// Constants can only do nil-vs-not-nil, since e.g. two strings "abc" and
      //// "abc" are equal constants in the type system but can be two different
      //// string pointers.
      //Type t1 = in1._val;
      //Type t2 = in2._val;
      //if( t1==Type.NIL || t1==Type.XNIL ) return EQ_OOP.vs_nil(t2,TypeInt.FALSE,TypeInt.TRUE);
      //if( t2==Type.NIL || t2==Type.XNIL ) return EQ_OOP.vs_nil(t1,TypeInt.FALSE,TypeInt.TRUE);
      //if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
      //return TypeInt.BOOL;
      throw unimpl();
    }
    @Override public Type apply( Type[] args ) { throw AA.unimpl(); }
  }


  public static class RandI64 extends PrimNode {
    public RandI64() { super("rand",TypeTuple.ALL_INT64,TypeStruct.INT); }
    @Override public Type value() {
      if( val(1).above_center() ) return make_wrap(TypeInt.BOOL.dual());
      if( val(1)==Type.ALL ) return TypeStruct.INT;
      TypeInt t = unwrap_i(val(1));
      if( TypeInt.INT64.dual().isa(t) && t.isa(TypeInt.INT64) )
        return make_wrap(t.meet(TypeNil.XNIL));
      return t.oob(TypeStruct.INT);
    }
    @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
    // Rands have hidden internal state; 2 Rands are never equal
    @Override public boolean equals(Object o) { return this==o; }
  }

  // Classic '&&' short-circuit.  Lazy in the RHS, so passed a 'thunk', a
  // zero-argument function to be evaluated if the LHS is true.
  public static class AndThen extends PrimNode {
    private static final TypeTuple ANDTHEN = TypeTuple.make(Type.CTRL, TypeMem.ALLMEM, Type.ALL, TypeFunPtr.THUNK); // {val tfp -> val }
    // Takes a value on the LHS, and a THUNK on the RHS.
    public AndThen() { super("&&",true/*lazy*/,ANDTHEN,TypeTuple.RET); }
    @Override public Type apply(Type[] ts) { throw unimpl(); }
    @Override public Type value() { return TypeTuple.RET; }
    // Expect this to inline everytime
    @Override public Node ideal_grow() {
      // Do not expand the base primitive, only clones.  This allows the base
      // primitive to inline as a primitive in all contexts.
      if( is_prim() ) return null; // Do not expand the base primitive, only clones
      if( len() <= ARG_IDX ) return null; // Already expanded
      // Once inlined, replace with an if/then/else diamond.
      Node ctl = in(CTL_IDX);
      Node mem = in(MEM_IDX);
      Node lhs = in(DSP_IDX);
      Node rhs = in(ARG_IDX);
      // Expand to if/then/else
      try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
        Node iff = X.xform(new IfNode(ctl,lhs));
        Node fal = X.xform(new CProjNode(iff,0));
        Node tru = X.xform(new CProjNode(iff,1));
        // Call on true branch; if false do not call.
        Node cal = X.xform(new CallNode(true,_badargs,tru,mem,rhs));
        Node cep = X.xform(new CallEpiNode(cal));
        Node ccc = X.xform(new CProjNode(cep));
        Node memc= X.xform(new MProjNode(cep));
        Node rez = X.xform(new  ProjNode(cep,AA.REZ_IDX));
        // Region merging results
        Node reg = X.init(new RegionNode(null,fal,ccc));
        Node phi = X.init(new PhiNode(Type.ALL,null,reg,Env.XNIL,rez ));
        Node phim= X.init(new PhiNode(TypeMem.ALLMEM,null,reg,mem,memc ));
        // Plug into self & trigger is_copy
        set_def(CTL_IDX,reg );
        set_def(MEM_IDX,phim);
        set_def(REZ_IDX,phi );
        pop();                  // Remove args, trigger is_copy
        return this;
      }
    }

    // Unify trailing result ProjNode with the AndTHen directly.
    @Override public boolean unify_proj( ProjNode proj, boolean test ) {
      assert proj._idx==REZ_IDX;
      return tvar().unify(proj.tvar(),test);
    }
    @Override public Node is_copy(int idx) {
      return _defs._len==ARG_IDX+1 ? null : in(idx);
    }
  }

  // Classic '||' short-circuit.  Lazy in the RHS, so passed a 'thunk', a
  // zero-argument function to be evaluated if the LHS is false.
  public static class OrElse extends PrimNode {
    private static final TypeTuple ORELSE = TypeTuple.make(Type.CTRL, TypeMem.ALLMEM, Type.ALL, TypeFunPtr.THUNK); // {val tfp -> val }
    // Takes a value on the LHS, and a THUNK on the RHS.
    public OrElse() { super("||",true/*lazy*/,ORELSE,TypeTuple.RET); }
    @Override public Type apply(Type[] ts) { throw unimpl(); }
    @Override public Type value() { return TypeTuple.RET; }
    // Expect this to inline everytime
    @Override public Node ideal_grow() {
      // Do not expand the base primitive, only clones.  This allows the base
      // primitive to inline as a primitive in all contexts.
      if( is_prim() ) return null; // Do not expand the base primitive, only clones
      if( len() <= ARG_IDX ) return null; // Already expanded
      Node ctl = in(CTL_IDX);
      Node mem = in(MEM_IDX);
      Node lhs = in(DSP_IDX);
      Node rhs = in(ARG_IDX);
      // Expand to if/then/else
      try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
        // Expand to if/then/else
        Node iff = X.xform(new IfNode(ctl,lhs));
        Node fal = X.xform(new CProjNode(iff,0));
        Node tru = X.xform(new CProjNode(iff,1));
        // Call on false branch; if true do not call.
        Node cal = X.xform(new CallNode(true,_badargs,fal,mem,rhs));
        Node cep = X.xform(new CallEpiNode(cal));
        Node ccc = X.xform(new CProjNode(cep));
        Node memc= X.xform(new MProjNode(cep));
        Node rez = X.xform(new  ProjNode(cep,AA.REZ_IDX));
        // Region merging results
        Node reg = X.init(new RegionNode(null,tru,ccc));
        Node phi = X.init(new PhiNode(Type.ALL,null,reg,lhs,rez ));
        Node phim= X.init(new PhiNode(TypeMem.ALLMEM,null,reg,mem,memc ));
        // Plug into self & trigger is_copy
        set_def(CTL_IDX,reg );
        set_def(MEM_IDX,phim);
        set_def(REZ_IDX,phi );
        pop();                // Remove args, trigger is_copy
        return this;
      }
    }
    // Unify trailing result ProjNode with the AndTHen directly.
    @Override public boolean unify_proj( ProjNode proj, boolean test ) {
      assert proj._idx==REZ_IDX;
      return tvar().unify(proj.tvar(),test);
    }
    @Override public Node is_copy(int idx) {
      return _defs._len==ARG_IDX+1 ? null : in(idx);
    }
  }

}
