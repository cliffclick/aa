package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

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

public abstract class PrimNode extends Node {
  public final String _name;    // Unique name (and program bits)
  public final TypeFunPtr _tfp; // FIDX, nargs, display argument, UNWRAPPED primitive return type
  public final TypeTuple _formals; // Formals are indexed by order NOT name and are unwrapped prims.
  public final TypeNil _ret;    // unwrapped primitive return
  public final boolean _is_lazy;// 2nd arg is lazy (thunked by parser)
  Parse[] _badargs;             // Filled in when inlined in CallNode
  public PrimNode( String name, TypeTuple formals, TypeNil ret ) { this(name,false,formals,ret); }
  public PrimNode( String name, boolean is_lazy, TypeTuple formals, TypeNil ret ) {
    _name = name;
    _is_lazy = is_lazy;
    int fidx = BitsFun.new_fidx(BitsFun.INTX);
    for( int i=DSP_IDX; i<formals._ts.length; i++ ) assert formals._ts[i] instanceof TypeNil || formals._ts[i]==Type.ANY;
    _formals = formals;
    _ret = ret;
    _tfp=TypeFunPtr.make(fidx,formals.len(),formals.at(DSP_IDX),ret);
    _badargs=null;
  }

  @Override public String label() { return _name; }

  // Int/Float/String primitives.
  public static final StructNode ZCLZ = new StructNode(0,false,null );
  public static final StructNode ZINT = new StructNode(0,false,null );
  public static final StructNode ZFLT = new StructNode(0,false,null );
  public static final StructNode ZSTR = new StructNode(0,false,null );
  public static final StructNode ZMATH= new StructNode(0,false,null );
  public static final NewNode PCLZ = new NewNode("TOP",BitsAlias.CLZX,true);
  public static final NewNode PINT = new NewNode("INT",BitsAlias.INTX,true);
  public static final NewNode PFLT = new NewNode("FLT",BitsAlias.FLTX,true);
  public static final NewNode PSTR = new NewNode("STR",BitsAlias.STRX,true); // String clazz, not strings
  public static final NewNode PMATH= new NewNode("MATH",BitsAlias.new_alias(BitsAlias.LOCX),true);
  public static TV3 IINT, IBOOL, IFLT, INFLT; // Integer, float instances

  private static PrimNode[] PRIMS = null; // All primitives

  public static PrimNode[] PRIMS() {
    if( PRIMS!=null ) return PRIMS;

    // int opers
    PrimNode[][] INTS = new PrimNode[][]{
      { new AddI64(), new AddIF64() },
      //{ new SubI64(), new SubIF64() },
      { new MulI64(), new MulIF64() },
      //{ new DivI64(), new DivIF64() },
      //{ new LT_I64(), new LT_IF64() },
      //{ new LE_I64(), new LE_IF64() },
      //{ new GT_I64(), new GT_IF64() },
      //{ new GE_I64(), new GE_IF64() },
      //{ new EQ_I64(), new EQ_IF64() },
      //{ new NE_I64(), new NE_IF64() },
      //{ new MinusI64() }, { new ModI64() },
      { new NotI64() },         // Triggers the shortcut for int printing
      //{ new AndI64() }, { new OrI64() },
      //{ new AndThen() }, { new OrElse() },
    };

    PrimNode[][] FLTS = new PrimNode[][]{
      { new AddF64(), new AddFI64() },
      //{ new SubFI64(), new SubF64() },
      { new MulFI64(), new MulF64() },
      //{ new DivF64(), new DivFI64() },
      //{ new LT_F64(), new LT_FI64() },
      //{ new GE_F64(), new GE_FI64() },
      //{ new LE_FI64(), new LE_F64() },
      //{ new GT_F64(), new GT_FI64() },
      //{ new EQ_F64(), new EQ_FI64() },
      //{ new NE_F64(), new NE_FI64() },
      //{ new MinusF64() },
      { new SinF64() },         // Triggers the shortcut for float printing
    };

    PrimNode[][] STRS = new PrimNode[][] {
      //{ new StrLen() }
    };

    // Other primitives, not binary operators
    PrimNode rand = new RandI64();
    PrimNode[] others = new PrimNode[] {
      // These are called like a function, so do not have a precedence
      //rand,
      //new ConvertI64F64(),

      //new EQ_OOP(), new NE_OOP(),
      //// These are balanced-ops, called by Parse.term()
      //new MemPrimNode.ReadPrimNode.LValueRead  (), // Read  an L-Value: (ary,idx) ==> elem
      //new MemPrimNode.ReadPrimNode.LValueWrite (), // Write an L-Value: (ary,idx,elem) ==> elem
      //new MemPrimNode.ReadPrimNode.LValueWriteFinal(), // Final Write an L-Value: (ary,idx,elem) ==> elem

      // These are unary ops, precedence determined outside 'Parse.expr'
      //new MemPrimNode.ReadPrimNode.LValueLength(), // The other array ops are "balanced ops" and use term() for precedence
    };

    ZCLZ.keep();
    ZINT.keep();
    ZFLT.keep();
    ZSTR.keep();

    // ClazzClazz
    ZCLZ.close();
    PCLZ.init();
    Env.SCP_0.mem(new StoreXNode(Env.SCP_0.mem(),Env.GVN.add_flow(PCLZ),ZCLZ,null));
    ZCLZ.set_tvar();

    // Gather
    Ary<PrimNode> allprims = new Ary<>(others);
    for( PrimNode prim : others ) allprims.push(prim);
    for( PrimNode[] prims : FLTS   ) for( PrimNode prim : prims ) allprims.push(prim);
    for( PrimNode[] prims : INTS   ) for( PrimNode prim : prims ) allprims.push(prim);

    // Build the int and float prototypes
    make_prim(ZFLT,"flt:",PFLT,FLTS);
    make_prim(ZINT,"int:",PINT,INTS);
    // String prototypes, uses ints, but ints do not depend on strs.
    make_prim(ZSTR,"str:",PSTR,STRS);

    // Math package
    Env.STK_0.add_fld("math",Access.Final,make_math(rand),null).xval();

    // TVar for wrapped primitive instance
    String[] ss  = new String[]{TypeFld.CLZ,TypeFld.PRIM};
    IINT  = new TVPtr(BitsAlias.EMPTY, new TVStruct(ss, new TV3[]{PINT.set_tvar(),new TVBase(TypeInt. INT64)},false));
    IBOOL = new TVPtr(BitsAlias.EMPTY, new TVStruct(ss, new TV3[]{PINT.set_tvar(),new TVBase(TypeInt. BOOL )},false));
    IFLT  = new TVPtr(BitsAlias.EMPTY, new TVStruct(ss, new TV3[]{PFLT.set_tvar(),new TVBase(TypeFlt. FLT64)},false));
    INFLT = new TVPtr(BitsAlias.EMPTY, new TVStruct(ss, new TV3[]{PFLT.set_tvar(),new TVBase(TypeFlt.NFLT64)},false));

    Env.ROOT.setDef(CTL_IDX,Env.CTL_0);
    Env.ROOT.setDef(MEM_IDX,Env.MEM_0);
    Env.ROOT.setDef(REZ_IDX,Env.ALL);


    // Set all TVars
    Env.ROOT.walk( n -> {
        Env.GVN.add_flow(n);
        if( n.has_tvar() ) n.set_tvar();
      });

    // Loop, setting initial types for all primitives
    Node n0;
    while( (n0=Env.GVN.pop_flow())!= null ) {
      n0.xval();
      n0.xliv();
      if( n0.has_tvar() && n0.unify(false) ) {
        n0.add_flow_defs();
        n0.add_flow_uses();
      }
    }
    assert Env.ROOT.walkReduce((n,x) -> chk(n) ? x : x+1 )==0;

    // Used for test cases
    MAX_PRIM_ALIAS = BitsAlias.NALL.tree().next_available_bit();
    MAX_PRIM_FIDX  = BitsFun  .NALL.tree().next_available_bit();

    PRIMS = allprims.asAry();
    return PRIMS;
  }

  static boolean chk(Node n) {
    boolean b0 = n.value()==n._val ;
    boolean b1 = n.live ()==n._live;
    boolean b2 = !n.unify(true);
    boolean b = b0 && b1 && b2;
    return b;
  }


  // Used for test cases; changes the golden-rule expected alias/fidx based on
  // how many get consumed by the primitives.  Means I can add/remove prims and
  // not have to renumber all the golden-rule tests.
  public static int MAX_PRIM_ALIAS, MAX_PRIM_FIDX;

  // Primitive wrapped as a simple function.
  // Fun Parm_dsp [Parm_y] prim Ret
  // No memory, no RPC.  Display is first arg.
  FunPtrNode as_fun( ) {
    assert !_is_lazy;           // No lazy operators here
    // Lazily discover operators
    if( is_oper() ) Oper.make(_name,false);
    FunNode fun = new FunNode(this,_name).init();
    ParmNode rpc = new ParmNode(0,fun,null,TypeRPC.ALL_CALL).init();
    // Make a Parm for every formal
    for(int i = DSP_IDX; i<_formals.len(); i++ )
      addDef(_formals.at(i)==Type.ANY ? null : new ParmNode(i,fun,null,wrap(_formals.at(i))).init());
    // The primitive, working on and producing wrapped prims
    init();
    // Return the result
    RetNode ret = new RetNode(fun,null/*no mem*/,this,rpc,fun).init();
    // FunPtr is UNBOUND here, will be bound when loaded thru a named struct to the Clazz.
    // Primitives all late-bind by default, so no BindFP here.
    return new FunPtrNode(_name,ret).init();
  }

  // Primitive wrapped as a simple function.
  // String memory, then DSP as first arg.
  FunPtrNode as_fun_str( ) {
    assert !_is_lazy;           // No lazy operators here
    // Lazily discover operators
    if( is_oper() ) Oper.make(_name,false);
    FunNode fun = new FunNode(this,_name).init();
    ParmNode rpc = new ParmNode(0      ,fun,null,TypeRPC.ALL_CALL).init();
    ParmNode mem = new ParmNode(MEM_IDX,fun,null,TypeMem.STRMEM  ).init();
    addDef(mem);
    // Make a Parm for every formal
    for(int i = DSP_IDX; i<_formals.len(); i++ )
      addDef(new ParmNode(i,fun,null,wrap(_formals.at(i))).init());
    // The primitive, working on and producing wrapped prims
    init();
    // Return the result
    RetNode ret = new RetNode(fun,mem,this,rpc,fun).init();
    // FunPtr is UNBOUND here, will be bound when loaded thru a named struct to the Clazz.
    // Primitives all late-bind by default, so no BindFP here.
    return new FunPtrNode(_name,ret).init();
  }

  // Make and install a primitive Clazz.
  private static void make_prim( StructNode clz, String clzname, NewNode ptr, PrimNode[][] primss ) {
    ScopeNode scp = Env.SCP_0;
    clz.add_fld(TypeFld.CLZ,Access.Final,PCLZ,null);
    for( PrimNode[] prims : primss ) {
      Node ptr0;
      if( prims.length==1 && !prims[0].is_oper() ) {
        ptr0 = prims[0].as_fun();
      } else {
        // Primitives are grouped into overload groups, where the 'this' or
        // display argument is always of the primitive type, and the other
        // arguments may vary, and the correct primitive is picked using
        // overload resolution.
        StructNode over = new StructNode(0,false,null );
        over.add_fld(TypeFld.CLZ,Access.Final,PCLZ,null);
        int cnt=0;
        for( PrimNode prim : prims ) {
          String fld = (""+cnt++).intern();
          over.add_fld(fld,Access.Final,prim.as_fun(),null);
        }
        over.init();
        over.close();
        // Some hacky name for the overload group; "f*" or "i!"
        String p = prims[0]._name;
        char op = p.charAt(0)=='_' ? p.charAt(1) : p.charAt(0);
        ptr0 = new NewNode(""+clzname.charAt(0)+op+":",BitsAlias.new_alias(BitsAlias.LOCX),true).init();
        scp.mem(new StoreXNode(scp.mem(),ptr0,over,null));
      }
      clz.add_fld(prims[0]._name,Access.Final,ptr0,null);
    }
    clz.close();
    Env.PROTOS.put(clzname,clz); // global mapping
    scp.mem(new StoreXNode(scp.mem(),Env.GVN.add_flow(ptr),clz,null));
  }

  // Build and install math package
  private static NewNode make_math(PrimNode rand) {
    ZMATH.add_fld(TypeFld.CLZ,Access.Final,PCLZ,null);
    Node pi = con(TypeFlt.PI.wrap());
    ZMATH.add_fld("pi",Access.Final,pi,null);
    ZMATH.add_fld(rand._name,Access.Final,rand.as_fun(),null);
    ZMATH.close().init();
    Env.SCP_0.mem(new StoreXNode(Env.SCP_0.mem(),PMATH,ZMATH,null));
    return PMATH;
  }

  // Apply uses the same alignment as the arguments, ParmNodes, _formals.
  abstract TypeNil apply( TypeNil[] args ); // Execute primitive
  // Pretty print short primitive signature based on first argument:
  //  + :{int int -> int }  ==>>   + :int
  //  + :{flt flt -> flt }  ==>>   + :flt
  //  + :{str str -> str }  ==>>   + :str
  // str:{int     -> str }  ==>>  str:int
  // str:{flt     -> str }  ==>>  str:flt
  // == :{ptr ptr -> int1}  ==>>  == :ptr
  private static final TypeNil[] TS = new TypeNil[ARG_IDX+1];
  @Override public Type value() {
    if( isKeep() ) return _val;
    // If all inputs are constants we constant-fold.  If any input is high, we
    // return high otherwise we return low.
    boolean is_con = true, has_high = false;
    for( int i=DSP_IDX; i<_formals.len(); i++ ) {
      if( _formals.at(i)==Type.ANY ) { // Formal is dead
        // TODO: Remove, only here for math.rand(2) instead of 2.rand
        TS[i-DSP_IDX] = null;
        continue;
      }
      TypeNil tformal = (TypeNil)_formals.at(i);
      Type actual = val(i-DSP_IDX);
      TypeNil ptn = unwrap(actual);
      if( ptn==null )return actual.oob(); // Not a primitive
      // Cap it at the formal
      TypeNil t = TS[i-DSP_IDX] = ptn==TypeNil.NIL ? TypeNil.NIL : (TypeNil)tformal.dual().meet(ptn);
      if( t != TypeNil.NIL && !t.is_con() ) {
        is_con = false;         // Some non-constant
        if( t.above_center() ) has_high=true;
      }
    }
    return wrap(is_con ? apply(TS) : (has_high ? _ret.dual() : _ret));
  }
  boolean is_oper() { return true; }

  // Wrap the PrimNode basic Type in a TMP->TS(.=ZINT, _=t).
  // Basically convert a `int` to a `Integer`
  public static TypeNil wrap( Type t ) {
    return switch( t ) {
      case TypeInt ti -> ti.wrap();
      case TypeFlt tf -> tf.wrap();
      case TypeNil tn -> tn;
      default -> throw TODO();
    };
  }
  public static TypeNil unwrap( Type t ) {
    if( !(t instanceof TypeMemPtr tmp) ) return null;
    return (TypeNil)tmp._obj.at(TypeFld.PRIM);
  }

  
  @Override public Node ideal_reduce() { return in(0)==this ? Env.ANY : null; }

  @Override public boolean has_tvar() { return true; }

  // In the test HM, all primitives are a Lambda without a body.  Here they are
  // effectively Applies/Calls and the primitive computes a result.
  @Override TV3 _set_tvar() {
    // All arguments are pre-unified to unique bases, wrapped in a primitive
    // with a clazz reference
    if( in(0) != null )
      in(0).set_tvar().unify(wrap_base(_formals.at(DSP_IDX)),false);
    // Skip dyntable, dead in all primitives
    assert in(1) == null;
    // 2-arg primitive sets next arg
    if( len()>2 ) {
      in(2).set_tvar().unify(wrap_base(_formals.at(ARG_IDX+1)),false);
      assert len()==3;
    }
      
    // Return is some primitive
    return wrap_base(_ret);
  }

  // Make a TV3
  public static TV3 wrap_base(Type rez) {
    if( rez == TypeInt. INT64 )  return  IINT;
    if( rez == TypeInt. BOOL  )  return IBOOL;
    if( rez == TypeFlt. FLT64 )  return  IFLT;
    if( rez == TypeFlt.NFLT64 )  return INFLT;
    throw TODO();
  }

  // All work done in set_tvar, no need to unify
  @Override public boolean unify( boolean test ) { return false; }

  @Override public ErrMsg err( boolean fast ) {
    for( int i=DSP_IDX; i<_formals.len(); i++ ) {
      if( _formals.at(i) == Type.ANY ) continue;
      Type tactual = val(i-DSP_IDX);
      TypeNil tformal = wrap(_formals.at(i));
      if( !tactual.isa(tformal) )
        return _badargs==null ? ErrMsg.BADARGS : ErrMsg.typerr(_badargs[i-DSP_IDX],tactual, tformal);
    }
    return null;
  }

  // Set escaping primitives into memory
  static TypeMem primitive_memory( Node def, TypeMem tmem ) {
    TypeStruct ts = TypeStruct.make(false,TypeNil.EXTERNAL,TypeFlds.EMPTY);
    tmem = tmem.set(BitsAlias.EXTX,ts);
    tmem = tmem.set(BitsAlias.STRX,TypeMemPtr.STRPTR._obj);
    tmem = tmem.set(PINT ._alias,TypeStruct.as_struct(ZINT ._val));
    tmem = tmem.set(PFLT ._alias,TypeStruct.as_struct(ZFLT ._val));
    tmem = tmem.set(PMATH._alias,TypeStruct.as_struct(ZMATH._val));
    ZINT .deps_add(def);
    ZFLT .deps_add(def);
    ZMATH.deps_add(def);
    return tmem;
  }


  // Prims are equal for same-name-same-signature (and same inputs).
  // E.g. float-minus of x and y is NOT the same as int-minus of x and y
  // despite both names being '-'.
  @Override int hash() { return (int)_formals._hash; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PrimNode p) ) return false;
    return Util.eq(_name,p._name) && _formals==p._formals;
  }

  //public static class ConvertI64F64 extends PrimNode {
  //  public ConvertI64F64() { super("flt",TypeTuple.INT64,TypeFlt.FLT64); }
  //  @Override Type apply( Type[] args ) {
  //    return make_flt((double)unwrap_ii(args[0]));
  //  }
  //}

  // 1Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim1OpF64 extends PrimNode {
    Prim1OpF64( String name ) { super(name,TypeTuple.FLT64,TypeFlt.FLT64); }
    @Override TypeFlt apply( TypeNil[] args ) {  return TypeFlt.con(op(args[0].getd()));  }
    abstract double op( double d );
  }

  static class MinusF64 extends Prim1OpF64 { MinusF64() { super("-_"); } double op( double d ) { return -d; } }

  static class SinF64 extends Prim1OpF64 {
    SinF64() { super("sin"); }
    @Override boolean is_oper() { return false; }
    @Override double op( double d ) { return Math.sin(d); }
  }

  // 1Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim1OpI64 extends PrimNode {
    Prim1OpI64( String name ) { super(name,TypeTuple.INT64,TypeInt.INT64); }
    @Override TypeInt apply( TypeNil[] args ) {  return TypeInt.con(op(args[0].getl()));  }
    abstract long op( long d );
  }

  static class MinusI64 extends Prim1OpI64 { MinusI64() { super("-_"); } long op( long x ) { return -x; } }
  static class NotI64 extends PrimNode {
    public NotI64() { super("!_",TypeTuple.INT64,TypeInt.BOOL); }
    @Override public TypeNil apply( TypeNil[] args ) {
      TypeNil t0 = args[0];
      if( t0._nil )
        return t0._sub
          ? TypeInt.BOOL.dual() // Choice nil and choice nint, could go either way
          : TypeInt.TRUE;       // Yes nil & ignore sub, so always true
      return t0._sub
        ? TypeNil.NIL           // not-nil, so always false
        : TypeInt.BOOL;         // Could go either way
    }
  }


  // 2Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim2OpF64 extends PrimNode {
    Prim2OpF64( String name ) { super(name,TypeTuple.FLT64_FLT64,TypeFlt.FLT64); }
    @Override TypeFlt apply( TypeNil[] args ) { return TypeFlt.con(op(args[0].getd(),args[2].getd())); }
    abstract double op( double x, double y );
  }

  static class AddF64 extends Prim2OpF64 { AddF64() { super("_+_"); } double op( double l, double r ) { return l+r; } }
  static class SubF64 extends Prim2OpF64 { SubF64() { super("_-_"); } double op( double l, double r ) { return l-r; } }
  static class MulF64 extends Prim2OpF64 { MulF64() { super("_*_"); } double op( double l, double r ) { return l*r; } }
  static class DivF64 extends Prim2OpF64 { DivF64() { super("_/_"); } double op( double l, double r ) { return l/r; } }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpF64 extends PrimNode {
    Prim2RelOpF64( String name ) { super(name,TypeTuple.FLT64_FLT64,TypeInt.BOOL); }
    @Override public TypeNil apply( TypeNil[] args ) { return op(args[0].getd(),args[1].getd()) ? TypeInt.TRUE : TypeNil.NIL ; }
    abstract boolean op( double x, double y );
  }

  public static class LT_F64 extends Prim2RelOpF64 { public LT_F64() { super("_<_" ); } boolean op( double l, double r ) { return l< r; } }
  public static class LE_F64 extends Prim2RelOpF64 { public LE_F64() { super("_<=_"); } boolean op( double l, double r ) { return l<=r; } }
  public static class GT_F64 extends Prim2RelOpF64 { public GT_F64() { super("_>_" ); } boolean op( double l, double r ) { return l> r; } }
  public static class GE_F64 extends Prim2RelOpF64 { public GE_F64() { super("_>=_"); } boolean op( double l, double r ) { return l>=r; } }
  public static class EQ_F64 extends Prim2RelOpF64 { public EQ_F64() { super("_==_"); } boolean op( double l, double r ) { return l==r; } }
  public static class NE_F64 extends Prim2RelOpF64 { public NE_F64() { super("_!=_"); } boolean op( double l, double r ) { return l!=r; } }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpFI64 extends PrimNode {
    Prim2RelOpFI64( String name ) { super(name,TypeTuple.FLT64_INT64,TypeInt.BOOL); }
    @Override public TypeNil apply( TypeNil[] args ) { return op(args[0].getd(),args[1].getl()) ? TypeInt.TRUE : TypeNil.NIL ; }
    abstract boolean op( double x, long y );
  }

  public static class LT_FI64 extends Prim2RelOpFI64 { public LT_FI64() { super("_<_" ); } boolean op( double l, long r ) { return l< r; } }
  public static class LE_FI64 extends Prim2RelOpFI64 { public LE_FI64() { super("_<=_"); } boolean op( double l, long r ) { return l<=r; } }
  public static class GT_FI64 extends Prim2RelOpFI64 { public GT_FI64() { super("_>_" ); } boolean op( double l, long r ) { return l> r; } }
  public static class GE_FI64 extends Prim2RelOpFI64 { public GE_FI64() { super("_>=_"); } boolean op( double l, long r ) { return l>=r; } }
  public static class EQ_FI64 extends Prim2RelOpFI64 { public EQ_FI64() { super("_==_"); } boolean op( double l, long r ) { return l==r; } }
  public static class NE_FI64 extends Prim2RelOpFI64 { public NE_FI64() { super("_!=_"); } boolean op( double l, long r ) { return l!=r; } }


  // 2Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim2OpI64 extends PrimNode {
    Prim2OpI64( String name ) { super(name,TypeTuple.INT64_INT64,TypeInt.INT64); }
    @Override public TypeNil apply( TypeNil[] args ) { return TypeInt.con(op(args[0].getl(),args[2].getl())); }
    abstract long op( long x, long y );
  }

  static class AddI64 extends Prim2OpI64 { AddI64() { super("_+_"); } long op( long l, long r ) { return l+r; } }
  static class SubI64 extends Prim2OpI64 { SubI64() { super("_-_"); } long op( long l, long r ) { return l-r; } }
  static class MulI64 extends Prim2OpI64 { MulI64() { super("_*_"); } long op( long l, long r ) { return l*r; } }
  static class DivI64 extends Prim2OpI64 { DivI64() { super("_/_"); } long op( long l, long r ) { return r==0 ? 0 : l/r; } } // Long division
  static class ModI64 extends Prim2OpI64 { ModI64() { super("_%_"); } long op( long l, long r ) { return r==0 ? 0 : l%r; } }

  abstract static class Prim2OpIF64 extends PrimNode {
    Prim2OpIF64( String name ) { super(name,TypeTuple.INT64_NFLT64,TypeFlt.FLT64); }
    @Override public TypeFlt apply( TypeNil[] args ) { return TypeFlt.con(op(args[0].getl(),args[2].getd())); }
    abstract double op( long x, double y );
  }
  static class AddIF64 extends Prim2OpIF64 { AddIF64() { super("_+_"); } double op( long l, double r ) { return l+r; } }
  static class SubIF64 extends Prim2OpIF64 { SubIF64() { super("_-_"); } double op( long l, double r ) { return l-r; } }
  static class MulIF64 extends Prim2OpIF64 { MulIF64() { super("_*_"); } double op( long l, double r ) { return l*r; } }
  static class DivIF64 extends Prim2OpIF64 { DivIF64() { super("_/_"); } double op( long l, double r ) { return l/r; } } // Float division, by 0 gives infinity

  abstract static class Prim2OpFI64 extends PrimNode {
    Prim2OpFI64( String name ) { super(name,TypeTuple.FLT64_INT64,TypeFlt.FLT64); }
    @Override public TypeFlt apply( TypeNil[] args ) { return TypeFlt.con(op(args[0].getd(),args[1].getl())); }
    abstract double op( double x, long y );
  }
  static class AddFI64 extends Prim2OpFI64 { AddFI64() { super("_+_"); } double op( double l, long r ) { return l+r; } }
  static class SubFI64 extends Prim2OpFI64 { SubFI64() { super("_-_"); } double op( double l, long r ) { return l-r; } }
  static class MulFI64 extends Prim2OpFI64 { MulFI64() { super("_*_"); } double op( double l, long r ) { return l*r; } }
  static class DivFI64 extends Prim2OpFI64 { DivFI64() { super("_/_"); } double op( double l, long r ) { return l/r; } } // Float division, by 0 gives infinity

  public static class AndI64 extends Prim2OpI64 {
    public AndI64() { super("_&_"); }
    // And can preserve bit-width
    @Override public TypeNil value() {
      Type t0 = val(0), t1 = val(1);
      // If either is high - results might fall to something reasonable
      if( t0.above_center() || t1.above_center() )
        return TypeInt.INT64.dual();
      if( t0==Type.ALL || t1==Type.ALL ) return TypeInt.INT64;
      // 0 AND anything is 0
      if( t0 == TypeNil.NIL || t1 == TypeNil.NIL ) return TypeNil.NIL;
      if( !(t0 instanceof TypeInt t0i) || !(t1 instanceof TypeInt t1i) )
        return TypeInt.INT64;
      // If both are constant ints, return the constant math.
      if( t0i.is_con() && t1i.is_con() ) {
        long i2 = t0i.getl() & t1i.getl();
        return i2==0 ? TypeNil.NIL : TypeInt.con(i2);
      }
      // Preserve width
      return t0i.minsize(t1i);
    }
    @Override long op( long l, long r ) { throw TODO(); }
  }

  public static class OrI64 extends Prim2OpI64 {
    public OrI64() { super("_|_"); }
    // And can preserve bit-width
    @Override long op( long l, long r ) { return l|r; }
  }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpI64 extends PrimNode {
    Prim2RelOpI64( String name ) { super(name,TypeTuple.INT64_INT64,TypeInt.BOOL); }
    @Override public TypeNil apply( TypeNil[] args ) { return op(args[0].getl(),args[1].getl()) ? TypeInt.TRUE : TypeNil.NIL; }
    abstract boolean op( long x, long y );
  }

  public static class LT_I64 extends Prim2RelOpI64 { public LT_I64() { super("_<_" ); } boolean op( long l, long r ) { return l< r; } }
  public static class LE_I64 extends Prim2RelOpI64 { public LE_I64() { super("_<=_"); } boolean op( long l, long r ) { return l<=r; } }
  public static class GT_I64 extends Prim2RelOpI64 { public GT_I64() { super("_>_" ); } boolean op( long l, long r ) { return l> r; } }
  public static class GE_I64 extends Prim2RelOpI64 { public GE_I64() { super("_>=_"); } boolean op( long l, long r ) { return l>=r; } }
  public static class EQ_I64 extends Prim2RelOpI64 { public EQ_I64() { super("_==_"); } boolean op( long l, long r ) { return l==r; } }
  public static class NE_I64 extends Prim2RelOpI64 { public NE_I64() { super("_!=_"); } boolean op( long l, long r ) { return l!=r; } }

  abstract static class Prim2RelOpIF64 extends PrimNode {
    Prim2RelOpIF64( String name ) { super(name,TypeTuple.INT64_NFLT64,TypeInt.BOOL); }
    @Override public TypeNil apply( TypeNil[] args ) { return op(args[0].getl(),args[1].getd()) ? TypeInt.TRUE : TypeNil.NIL; }
    abstract boolean op( long x, double y );
  }

  public static class LT_IF64 extends Prim2RelOpIF64 { public LT_IF64() { super("_<_" ); } boolean op( long l, double r ) { return l< r; } }
  public static class LE_IF64 extends Prim2RelOpIF64 { public LE_IF64() { super("_<=_"); } boolean op( long l, double r ) { return l<=r; } }
  public static class GT_IF64 extends Prim2RelOpIF64 { public GT_IF64() { super("_>_" ); } boolean op( long l, double r ) { return l> r; } }
  public static class GE_IF64 extends Prim2RelOpIF64 { public GE_IF64() { super("_>=_"); } boolean op( long l, double r ) { return l>=r; } }
  public static class EQ_IF64 extends Prim2RelOpIF64 { public EQ_IF64() { super("_==_"); } boolean op( long l, double r ) { return l==r; } }
  public static class NE_IF64 extends Prim2RelOpIF64 { public NE_IF64() { super("_!=_"); } boolean op( long l, double r ) { return l!=r; } }


  public static class EQ_OOP extends PrimNode {
    public EQ_OOP() { super("_==_",TypeTuple.OOP_OOP,TypeInt.BOOL); }
    @Override public TypeStruct value() {
      //if( is_keep() ) return _val;
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
      //if( t1==Type.NIL || t1==Type.NIL ) return vs_nil(t2,TypeInt.TRUE,TypeInt.FALSE);
      //if( t2==Type.NIL || t2==Type.NIL ) return vs_nil(t1,TypeInt.TRUE,TypeInt.FALSE);
      //if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
      //return TypeInt.BOOL;
      throw TODO();
    }
    @Override public TypeNil apply( TypeNil[] args ) { throw AA.TODO(); }
    static Type vs_nil( Type tx, Type t, Type f ) {
      if( tx==TypeNil.NIL ) return t;
      //if( tx.above_center() ) return tx.isa(TypeNil.NIL) ? TypeInt.BOOL.dual() : f;
      //return tx.must_nil() ? TypeInt.BOOL : f;
      throw TODO();
    }
  }

  public static class NE_OOP extends PrimNode {
    public NE_OOP() { super("_!=_",TypeTuple.OOP_OOP,TypeInt.BOOL); }
    @Override public TypeStruct value() {
      //if( is_keep() ) return _val;
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
      //if( t1==Type.NIL || t1==Type.NIL ) return EQ_OOP.vs_nil(t2,TypeInt.FALSE,TypeInt.TRUE);
      //if( t2==Type.NIL || t2==Type.NIL ) return EQ_OOP.vs_nil(t1,TypeInt.FALSE,TypeInt.TRUE);
      //if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
      //return TypeInt.BOOL;
      throw TODO();
    }
    @Override public TypeNil apply( TypeNil[] args ) { throw AA.TODO(); }
  }


  public static class StrLen extends PrimNode {
    public StrLen() { super("#_",TypeTuple.STR,TypeInt.INT64); }
    @Override public TypeNil apply( TypeNil[] args ) { throw TODO(); }
    @Override public Type value() {
      if( !(val(1) instanceof TypeMemPtr tmp) ||
          !tmp.is_str() )
        return val(1).oob(TypeInt.INT64);
      return tmp.oob(TypeInt.INT64);
    }
    @Override FunPtrNode as_fun() { return as_fun_str(); }
    // In the test HM, all primitives are a Lambda without a body.  Here they are
    // effectively Applies/Calls and the primitive computes a result.
    @Override TV3 _set_tvar() {
      // All arguments are pre-unified to unique bases, wrapped in a
      // primitive with a clazz reference
      for( int i=DSP_IDX; i<_formals.len(); i++ )
        if( _formals.at(i)!=Type.ANY )
          // Only StrLen has a Memory input, so the offset here is off-by-one
          // from the default _set_tvar
          in(i-MEM_IDX).set_tvar().unify(wrap_base(_formals.at(i)),false);
      // Return is some primitive
      return wrap_base(_ret);
    }
  }


  public static class RandI64 extends PrimNode {
    public RandI64() { super("rand",TypeTuple.make(Type.CTRL, TypeMem.ALLMEM, Type.ANY, Type.ANY, TypeInt.INT64),TypeInt.INT64); }
    @Override boolean is_oper() { return false; }
    @Override public TypeNil apply( TypeNil[] args ) { return TypeInt.INT64;  }
    // Rands have hidden internal state; 2 Rands are never equal
    @Override public boolean equals(Object o) { return this==o; }
  }

  // Classic '&&' short-circuit.  Lazy in the RHS, so passed a 'thunk', a
  // zero-argument function to be evaluated if the LHS is true.
  // HM type is: { Int { -> A } -> A? }
  public static class AndThen extends PrimNode {
    private static final TypeTuple ANDTHEN = TypeTuple.make(Type.CTRL, TypeMem.ALLMEM, TypeInt.INT64, TypeFunPtr.THUNK); // {val tfp -> val }
    // Takes a value on the LHS, and a THUNK on the RHS.
    public AndThen() { super("_&&_",true/*lazy*/,ANDTHEN,TypeNil.SCALAR); _live = TypeMem.ALLMEM; }
    @Override public TypeNil apply(TypeNil[] ts) { throw TODO(); }
    @Override FunPtrNode as_fun() {
      Oper.make(_name,_is_lazy);
      FunNode fun = new FunNode(this,_name).init();
      ParmNode rpc = new ParmNode(CTL_IDX,fun,null,TypeRPC.ALL_CALL).init();
      ParmNode mem = new ParmNode(MEM_IDX,fun,null,TypeMem.ALLMEM  ).init();
      // Since looked-up in the INT clazz, display is integer
      // TODO: Should be in the TypeNil.SCALAR lookup, the parent class of TypeInt.
      // TODO: Nested clazz lookup.
      ParmNode lhs = new ParmNode(DSP_IDX,fun,null,TypeInt.INT64   ).init();
      ParmNode rhs = new ParmNode(ARG_IDX,fun,null,TypeFunPtr.THUNK).init();
      Node iff = new IfNode(fun,lhs).init();
      Node fal = new CProjNode(iff,0).init();
      Node tru = new CProjNode(iff,1).init();
      // Call on true branch; if false do not call.
      Node dsp = new FP2DSPNode(rhs,null).init();
      Node cal = new CallNode(true,_badargs,tru,mem,dsp,rhs).init();
      Node cep = new CallEpiNode(cal).init();
      Node ccc = new CProjNode(cep).init();
      Node memc= new MProjNode(cep).init();
      Node rez = new  ProjNode(cep,AA.REZ_IDX).init();
      // Region merging results
      Node reg = new RegionNode(null,fal,ccc).init();
      Node phi = new PhiNode(Type.ALL,null,reg,Env.NIL,rez ).init();
      Node phim= new PhiNode(TypeMem.ALLMEM,null,reg,mem,memc ).init();
      // Plug into return
      RetNode ret = new RetNode(reg,phim,phi,rpc,fun).init();
      return new FunPtrNode(_name,ret).init();
    }
  }

  // Classic '||' short-circuit.  Lazy in the RHS, so passed a 'thunk', a
  // zero-argument function to be evaluated if the LHS is false.
  // HM type is: { Int { -> Int } -> Int }
  public static class OrElse extends PrimNode {
    private static final TypeTuple ORELSE = TypeTuple.make(Type.CTRL, TypeMem.ALLMEM, TypeInt.INT64, TypeFunPtr.THUNK); // {val tfp -> val }
    // Takes a value on the LHS, and a THUNK on the RHS.
    public OrElse() { super("_||_",true/*lazy*/,ORELSE,TypeNil.SCALAR); _live = TypeMem.ALLMEM; }
    //@Override public boolean is_mem() { return true; }
    @Override public TypeNil apply(TypeNil[] ts) { throw TODO(); }
    @Override FunPtrNode as_fun() {
      Oper.make(_name,_is_lazy);
      FunNode fun = new FunNode(this,_name).init();
      ParmNode rpc = new ParmNode(CTL_IDX,fun,null,TypeRPC.ALL_CALL).init();
      ParmNode mem = new ParmNode(MEM_IDX,fun,null,TypeMem.ALLMEM  ).init();
      // Since looked-up in the INT clazz, display is integer
      // TODO: Should be in the TypeNil.SCALAR lookup, the parent class of TypeInt.
      // TODO: Nested clazz lookup.
      ParmNode lhs = new ParmNode(DSP_IDX,fun,null,TypeInt.INT64   ).init();
      ParmNode rhs = new ParmNode(ARG_IDX,fun,null,TypeFunPtr.THUNK).init();
      Node iff = new IfNode(fun,lhs).init();
      Node fal = new CProjNode(iff,0).init();
      Node tru = new CProjNode(iff,1).init();
      // Call on false branch; if true do not call.
      Node dsp = new FP2DSPNode(rhs,null).init();
      Node cal = new CallNode(true,_badargs,fal,mem,dsp,rhs).init();
      Node cep = new CallEpiNode(cal).init();
      Node ccc = new CProjNode(cep).init();
      Node memc= new MProjNode(cep).init();
      Node rez = new  ProjNode(cep,AA.REZ_IDX).init();
      // Region merging results
      Node reg = new RegionNode(null,tru,ccc).init();
      Node phi = new PhiNode(Type.ALL,null,reg,lhs,rez ).init();
      Node phim= new PhiNode(TypeMem.ALLMEM,null,reg,mem,memc ).init();
      // Plug into return
      RetNode ret = new RetNode(reg,phim,phi,rpc,fun).init();
      return new FunPtrNode(_name,ret).init();
    }
  }

}
