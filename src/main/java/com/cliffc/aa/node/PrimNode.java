package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.util.Ary;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import static com.cliffc.aa.AA.*;

// Primitives can be used as an internal operator (their apply() call does the
// primitive operation).  Primitives are wrapped as functions when returned
// from Env lookup, although the immediate lookup+apply is optimized to just
// make a new primitive.  See FunNode for function Node structure.
//
// Fun/Parm-per-arg/Prim/Ret
//
public abstract class PrimNode extends Node {
  public final String _name;    // Unique name (and program bits)
  final TypeFunSig _sig;        // Argument types; ctrl, mem, disp, normal args
  final TypeFunPtr _tfp;        // FIDX, nargs, display argument, return type
  Parse[] _badargs;             // Filled in when inlined in CallNode
  byte _op_prec;                // Operator precedence, computed from table.  Generally 1-9.
  public boolean _thunk_rhs;    // Thunk (delay) right-hand-argument.
  public PrimNode( String name, TypeStruct formals, Type ret ) {
    super(OP_PRIM);
    _name = name;
    assert formals.fld_find("^")==null; // No display
    int fidx = BitsFun.new_fidx();
    _sig=TypeFunSig.make(formals,ret);
    _tfp=TypeFunPtr.make(BitsFun.make0(fidx),formals.nargs(),TypeMemPtr.NO_DISP,ret);
    _badargs=null;
    _op_prec = -1;              // Not set yet
    _thunk_rhs=false;
  }

  private static PrimNode[] PRIMS = null; // All primitives
  public static PrimNode[][] PRECEDENCE = null;  // Just the binary operators, grouped by precedence
  public static String  [][] PREC_TOKS  = null;  // Just the binary op tokens, grouped by precedence
  public static String  []   PRIM_TOKS  = null;  // Primitive tokens, longer first for greedy token search

  public static PrimNode[] PRIMS() {
    if( PRIMS!=null ) return PRIMS;

    // Binary-operator primitives, sorted by precedence.
    PRECEDENCE = new PrimNode[][]{

      {new MulF64(), new DivF64(), new MulI64(), new DivI64(), new ModI64(), },

      {new AddF64(), new SubF64(), new AddI64(), new SubI64() },

      {new LT_F64(), new LE_F64(), new GT_F64(), new GE_F64(),
       new LT_I64(), new LE_I64(), new GT_I64(), new GE_I64(),},

      {new EQ_F64(), new NE_F64(), new EQ_I64(), new NE_I64(), new EQ_OOP(), new NE_OOP(), },

      {new AndI64(), },

      {new OrI64(), },

      {new AndThen(), },

      {new OrElse(), },

    };

    // Other primitives, not binary operators
    PrimNode[] others = new PrimNode[] {
      // These are called like a function, so do not have a precedence
      new RandI64(),

      new ConvertInt64F64(),

      // These are balanced-ops, called by Parse.term()
      new MemPrimNode.ReadPrimNode.LValueRead  (), // Read  an L-Value: (ary,idx) ==> elem
      new MemPrimNode.ReadPrimNode.LValueWrite (), // Write an L-Value: (ary,idx,elem) ==> elem
      new MemPrimNode.ReadPrimNode.LValueWriteFinal(), // Final Write an L-Value: (ary,idx,elem) ==> elem
    };

    // These are unary ops, precedence determined outside 'Parse.expr'
    PrimNode[] uniops = new PrimNode[] {
      new MemPrimNode.ReadPrimNode.LValueLength(), // The other array ops are "balanced ops" and use term() for precedence
      new MinusF64(),
      new MinusI64(),
      new Not(),
    };

    Ary<PrimNode> allprims = new Ary<>(others);
    for( PrimNode prim : uniops ) allprims.push(prim);
    for( PrimNode[] prims : PRECEDENCE )
      for( PrimNode prim : prims )
        allprims.push(prim);
    PRIMS = allprims.asAry();

    // Compute precedence from table
    int max_prec = PRECEDENCE.length;
    for( int p=0; p<PRECEDENCE.length; p++ )
      for( PrimNode n : PRECEDENCE[p] )
        n._op_prec = (byte)(max_prec-p);
    // Not used to determine precedence, just a uniop flag
    for( PrimNode prim : uniops ) prim._op_prec = (byte)max_prec;

    // Compute greedy primitive names, without regard to precedence.
    // Example from Java: >,>=,>>,>>=,>>>,>>>= are all valid tokens.
    HashSet<String> hash = new HashSet<>(); // Remove dups
    for( PrimNode[] prims : PRECEDENCE )
      for( PrimNode prim : prims )
        hash.add(prim._name);
    ArrayList<String> list = new ArrayList<>(hash);
    Collections.sort(list);     // Longer strings on the right
    Collections.reverse(list);  // Longer strings on the left, match first.
    PRIM_TOKS = list.toArray(new String[0]);

    // Compute precedence token groupings for parser
    PREC_TOKS = new String[max_prec+1][];
    for( int p=0; p<max_prec; p++ ) {
      String[] toks = PREC_TOKS[p+1] = new String[PRECEDENCE[max_prec-1-p].length];
      for( int i=0; i<toks.length; i++ )
        toks[i] = PRECEDENCE[max_prec-1-p][i]._name;
    }

    return PRIMS;
  }

  // All primitives are effectively H-M Applies with a hidden internal Lambda.
  @Override public boolean unify( Work work ) {
    boolean progress = false;
    for( TypeFld fld : _sig._formals.flds() )
      progress |= prim_unify(tvar(fld._order),fld._t,work);
    progress |= prim_unify(tvar(),_tfp._ret,work);
    return progress;
  }
  private boolean prim_unify(TV2 arg, Type t, Work work) {
    if( arg.is_base() && t.isa(arg._type) ) return false;
    if( arg.is_err() ) return false;
    if( work==null ) return true;
    return arg.unify(TV2.make_base(this, arg._type==null ? t : t.meet(arg._type), "Prim_unify"), work);
  }


  // Apply types are 1-based (same as the incoming node index), and not
  // zero-based (not same as the _formals and _args fields).
  public abstract Type apply( Type[] args ); // Execute primitive
  // Pretty print short primitive signature based on first argument:
  //  + :{int int -> int }  ==>>   + :int
  //  + :{flt flt -> flt }  ==>>   + :flt
  //  + :{str str -> str }  ==>>   + :str
  // str:{int     -> str }  ==>>  str:int
  // str:{flt     -> str }  ==>>  str:flt
  // == :{ptr ptr -> int1}  ==>>  == :ptr
  @Override public String xstr() { return _name+":"+_sig._formals.fld_idx(ARG_IDX)._t; }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type[] ts = Types.get(_defs._len); // 1-based
    // If all inputs are constants we constant-fold.  If any input is high, we
    // return high otherwise we return low.
    boolean is_con = true, has_high = false;
    for( TypeFld fld : _sig._formals.flds() ) {
      Type tactual = ts[fld._order] = val(fld._order);
      Type tformal = fld._t;
      Type t = tformal.dual().meet(tactual);
      if( !t.is_con() ) {
        is_con = false;         // Some non-constant
        if( t.above_center() ) has_high=true;
      }
    }
    Type rez = _tfp._ret;
    Type rez2 = is_con ? apply(ts) : (has_high ? rez.dual() : rez);
    Types.free(ts);
    return rez2;
  }

  @Override public Node ideal_reduce() {
    if( _live != TypeMem.DEAD ) return null;
    Node progress=null;
    for( int i=ARG_IDX; i<_defs._len; i++ )
      if( in(i)!=Env.ANY ) progress=set_def(i,Env.ANY);
    return progress;
  }


  @Override public ErrMsg err( boolean fast ) {
    for( TypeFld fld : _sig._formals.flds() ) {
      Type tactual = val(fld._order);
      Type tformal = fld._t;
      if( !tactual.isa(tformal) )
        return _badargs==null ? ErrMsg.BADARGS : ErrMsg.typerr(_badargs[fld._order-ARG_IDX],tactual,null,tformal);
    }
    return null;
  }
  // Prims are equal for same-name-same-signature (and same inputs).
  // E.g. float-minus of x and y is NOT the same as int-minus of x and y
  // despite both names being '-'.
  @Override public int hashCode() { return super.hashCode()+_name.hashCode()+_sig._hash; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PrimNode) ) return false;
    PrimNode p = (PrimNode)o;
    return _name.equals(p._name) && _sig==p._sig;
  }

  // Called during basic Env creation and making of type constructors, this
  // wraps a PrimNode as a full 1st-class function to be passed about or
  // assigned to variables.
  @Override public FunPtrNode clazz_node( ) {
    // Find the same clazz node with op_prec set
    PrimNode that=null;
    for( PrimNode p : PRIMS() )
      if( p.getClass() == getClass() )
        { that=p; break; }      // Found an original PrimNode with op_prec set
    assert that != null;
    kill(); // Kill self, use one from primitive table that has op_prec set

    try(GVNGCM.Build<FunPtrNode> X = Env.GVN.new Build<>()) {
      assert that._defs._len==0 && that._uses._len==0;
      // Extra '$' in name copies the op_prec one inlining level from clazz_node into the _prim.aa
      FunNode fun = new FunNode(("$"+_name).intern(),that); // No callers (yet)
      fun._val = Type.CTRL;
      fun._java_fun = true;
      Node rpc = X.xform(new ParmNode(TypeRPC.ALL_CALL,null,fun,0,"rpc"));
      that.add_def(_thunk_rhs ? fun : null);   // Control for the primitive in slot 0
      Node mem = X.xform(new ParmNode(TypeMem.MEM,null,fun,MEM_IDX," mem"));
      if( _thunk_rhs ) that.add_def(mem);  // Memory if thunking
      while( that.len() < _sig._formals.nargs() ) that.add_def(null);
      for( TypeFld fld : _sig._formals.flds() )
        that.set_def(fld._order,X.xform(new ParmNode(fld._t,null,fun,fld._order,fld._fld)));
      that = (PrimNode)X.xform(that);
      Node ctl,rez;
      if( _thunk_rhs ) {
        ctl = X.xform(new CProjNode(that));
        mem = X.xform(new MProjNode(that));
        rez = X.xform(new  ProjNode(that,AA.REZ_IDX));
        Env.GVN.add_grow(that);
      } else {
        ctl = fun;
        rez = that;
      }
      // Functions return the set of *modified* memory.  Most PrimNodes never
      // *modify* memory (see Intrinsic*Node for some primitives that *modify*
      // memory).  Thunking (short circuit) prims return both memory and a value.
      RetNode ret = (RetNode)X.xform(new RetNode(ctl,mem,rez,rpc,fun));
      // No closures are added to primitives
      return (X._ret = (FunPtrNode)X.xform(new FunPtrNode(_name,ret)));
    }
  }


  // --------------------
  // Default name constructor using a single tuple type
  static class ConvertTypeName extends PrimNode {
    ConvertTypeName(Type from, Type to, Parse badargs, Node p) {
      super(to._name,TypeStruct.args(from),to);
      _badargs = new Parse[]{badargs};
      add_def(null);
      add_def(null);
      add_def(null);
      add_def(p);
    }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type[] ts = Types.get(_defs._len);
      for( int i=ARG_IDX; i<_defs._len; i++ )
        ts[i] = _defs.at(i)._val;
      Type t = apply(ts);     // Apply (convert) even if some args are not constant
      Types.free(ts);
      return t;
    }
    @Override public Type apply( Type[] args ) {
      Type actual = args[ARG_IDX];
      if( actual==Type.ANY || actual==Type.ALL ) return actual;
      Type formal = _sig.arg(ARG_IDX)._t;
      // Wrapping function will not inline if args are in-error
      assert actual.isa(formal);
      return actual.set_name(_tfp._ret._name);
    }
    @Override public ErrMsg err( boolean fast ) {
      Type actual = val(ARG_IDX);
      Type formal = _sig.arg(ARG_IDX)._t;
      if( !actual.isa(formal) ) // Actual is not a formal
        return ErrMsg.typerr(_badargs[0],actual,null,formal);
      return null;
    }
  }

  static class ConvertInt64F64 extends PrimNode {
    ConvertInt64F64() { super("flt64",TypeStruct.INT64,TypeFlt.FLT64); }
    @Override public Type apply( Type[] args ) { return TypeFlt.con((double)args[1].getl()); }
  }


  // Takes in a Scalar and Names it.
  public static FunPtrNode convertTypeName( Type from, Type to, Parse badargs, FunNode parfun ) {
    try(GVNGCM.Build<FunPtrNode> X = Env.GVN.new Build<>()) {
      TypeStruct formals = TypeStruct.args(from);
      TypeFunSig sig = TypeFunSig.make(formals,to);
      Node ctl = Env.FILE._scope;
      FunNode fun = X.init2((FunNode)new FunNode(to._name,sig,-1,false,parfun).add_def(ctl));
      Node rpc = X.xform(new ParmNode(CTL_IDX," rpc",fun,Env.ALL_CALL,null));
      Node ptr = X.xform(new ParmNode(ARG_IDX,"x",fun,(ConNode)Node.con(from),badargs));
      Node mem = X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
      Node cvt = X.xform(new ConvertTypeName(from,to,badargs,ptr));
      RetNode ret = (RetNode)X.xform(new RetNode(fun,mem,cvt,rpc,fun));
      Env.SCP_0.add_def(ret);
      return (X._ret = X.init2(new FunPtrNode(to._name,ret)));
    }
  }


  // 1Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim1OpF64 extends PrimNode {
    Prim1OpF64( String name ) { super(name,TypeStruct.FLT64,TypeFlt.FLT64); }
    public Type apply( Type[] args ) { return TypeFlt.con(op(args[ARG_IDX].getd())); }
    abstract double op( double d );
  }

  static class MinusF64 extends Prim1OpF64 {
    MinusF64() { super("-"); }
    @Override double op( double d ) { return -d; }
  }

  // 1Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim1OpI64 extends PrimNode {
    Prim1OpI64( String name ) { super(name,TypeStruct.INT64,TypeInt.INT64); }
    @Override public Type apply( Type[] args ) { return TypeInt.con(op(args[ARG_IDX].getl())); }
    abstract long op( long d );
  }

  public static class MinusI64 extends Prim1OpI64 {
    public MinusI64() { super("-"); }
    @Override long op( long x ) { return -x; }
  }

  // 2Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim2OpF64 extends PrimNode {
    Prim2OpF64( String name ) { super(name,TypeStruct.FLT64_FLT64,TypeFlt.FLT64); }
    @Override public Type apply( Type[] args ) { return TypeFlt.con(op(args[ARG_IDX].getd(),args[ARG_IDX+1].getd())); }
    abstract double op( double x, double y );
  }

  public static class AddF64 extends Prim2OpF64 {
    public AddF64() { super("+"); }
    double op( double l, double r ) { return l+r; }
  }

  public static class SubF64 extends Prim2OpF64 {
    public SubF64() { super("-"); }
    double op( double l, double r ) { return l-r; }
  }

  public static class MulF64 extends Prim2OpF64 {
    public MulF64() { super("*"); }
    @Override double op( double l, double r ) { return l*r; }
  }

  public static class DivF64 extends Prim2OpF64 {
    public DivF64() { super("/"); }
    @Override double op( double l, double r ) { return l/r; }
  }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpF64 extends PrimNode {
    Prim2RelOpF64( String name ) { super(name,TypeStruct.FLT64_FLT64,TypeInt.BOOL); }
    @Override public Type apply( Type[] args ) { return op(args[ARG_IDX].getd(),args[ARG_IDX+1].getd())?TypeInt.TRUE:TypeInt.FALSE; }
    abstract boolean op( double x, double y );
  }

  public static class LT_F64 extends Prim2RelOpF64 { public LT_F64() { super("<" ); } boolean op( double l, double r ) { return l< r; } }
  public static class LE_F64 extends Prim2RelOpF64 { public LE_F64() { super("<="); } boolean op( double l, double r ) { return l<=r; } }
  public static class GT_F64 extends Prim2RelOpF64 { public GT_F64() { super(">" ); } boolean op( double l, double r ) { return l> r; } }
  public static class GE_F64 extends Prim2RelOpF64 { public GE_F64() { super(">="); } boolean op( double l, double r ) { return l>=r; } }
  public static class EQ_F64 extends Prim2RelOpF64 { public EQ_F64() { super("=="); } boolean op( double l, double r ) { return l==r; } }
  public static class NE_F64 extends Prim2RelOpF64 { public NE_F64() { super("!="); } boolean op( double l, double r ) { return l!=r; } }


  // 2Ops have uniform input/output types, so take a shortcut on name printing
  abstract static class Prim2OpI64 extends PrimNode {
    Prim2OpI64( String name ) { super(name,TypeStruct.INT64_INT64,TypeInt.INT64); }
    @Override public Type apply( Type[] args ) { return TypeInt.con(op(args[ARG_IDX].getl(),args[ARG_IDX+1].getl())); }
    abstract long op( long x, long y );
  }

  public static class AddI64 extends Prim2OpI64 {
    public AddI64() { super("+"); }
    @Override long op( long l, long r ) { return l+r; }
  }

  public static class SubI64 extends Prim2OpI64 {
    public SubI64() { super("-"); }
    @Override long op( long l, long r ) { return l-r; }
  }

  public static class MulI64 extends Prim2OpI64 {
    public MulI64() { super("*"); }
    @Override long op( long l, long r ) { return l*r; }
  }

  public static class DivI64 extends Prim2OpI64 {
    public DivI64() { super("/"); }
    @Override long op( long l, long r ) { return l/r; } // Long division
  }

  public static class ModI64 extends Prim2OpI64 {
    public ModI64() { super("%"); }
    @Override long op( long l, long r ) { return l%r; }
  }

  public static class AndI64 extends Prim2OpI64 {
    public AndI64() { super("&"); }
    // And can preserve bit-width
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type t1 = val(ARG_IDX), t2 = val(ARG_IDX+1);
      // 0 AND anything is 0
      if( t1 == Type. NIL || t2 == Type. NIL ) return Type. NIL;
      if( t1 == Type.XNIL || t2 == Type.XNIL ) return Type.XNIL;
      // If either is high - results might fall to something reasonable
      if( t1.above_center() || t2.above_center() )
        return TypeInt.INT64.dual();
      // Both are low-or-constant, and one is not valid - return bottom result
      if( !t1.isa(TypeInt.INT64) || !t2.isa(TypeInt.INT64) )
        return TypeInt.INT64;
      // If both are constant ints, return the constant math.
      if( t1.is_con() && t2.is_con() )
        return TypeInt.con(t1.getl() & t2.getl());
      if( !(t1 instanceof TypeInt) || !(t2 instanceof TypeInt) )
        return TypeInt.INT64;
      // Preserve width
      return ((TypeInt)t1).minsize((TypeInt)t2);
    }
    @Override long op( long l, long r ) { return l&r; }
  }

  public static class OrI64 extends Prim2OpI64 {
    public OrI64() { super("|"); }
    // And can preserve bit-width
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type t1 = val(ARG_IDX), t2 = val(ARG_IDX+1);
      // 0 OR anything is that thing
      if( t1 == Type.NIL || t1 == Type.XNIL ) return t2;
      if( t2 == Type.NIL || t2 == Type.XNIL ) return t1;
      // If either is high - results might fall to something reasonable
      if( t1.above_center() || t2.above_center() )
        return TypeInt.INT64.dual();
      // Both are low-or-constant, and one is not valid - return bottom result
      if( !t1.isa(TypeInt.INT64) || !t2.isa(TypeInt.INT64) )
        return TypeInt.INT64;
      // If both are constant ints, return the constant math.
      if( t1.is_con() && t2.is_con() )
        return TypeInt.con(t1.getl() | t2.getl());
      if( !(t1 instanceof TypeInt) || !(t2 instanceof TypeInt) )
        return TypeInt.INT64;
      // Preserve width
      return ((TypeInt)t1).maxsize((TypeInt)t2);
    }
    @Override long op( long l, long r ) { return l&r; }
  }

  // 2RelOps have uniform input types, and bool output
  abstract static class Prim2RelOpI64 extends PrimNode {
    Prim2RelOpI64( String name ) { super(name,TypeStruct.INT64_INT64,TypeInt.BOOL); }
    @Override public Type apply( Type[] args ) { return op(args[ARG_IDX].getl(),args[ARG_IDX+1].getl())?TypeInt.TRUE:TypeInt.FALSE; }
    abstract boolean op( long x, long y );
  }

  public static class LT_I64 extends Prim2RelOpI64 { public LT_I64() { super("<" ); } boolean op( long l, long r ) { return l< r; } }
  public static class LE_I64 extends Prim2RelOpI64 { public LE_I64() { super("<="); } boolean op( long l, long r ) { return l<=r; } }
  public static class GT_I64 extends Prim2RelOpI64 { public GT_I64() { super(">" ); } boolean op( long l, long r ) { return l> r; } }
  public static class GE_I64 extends Prim2RelOpI64 { public GE_I64() { super(">="); } boolean op( long l, long r ) { return l>=r; } }
  public static class EQ_I64 extends Prim2RelOpI64 { public EQ_I64() { super("=="); } boolean op( long l, long r ) { return l==r; } }
  public static class NE_I64 extends Prim2RelOpI64 { public NE_I64() { super("!="); } boolean op( long l, long r ) { return l!=r; } }


  public static class EQ_OOP extends PrimNode {
    public EQ_OOP() { super("==",TypeMemPtr.OOP_OOP,TypeInt.BOOL); }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      // Oop-equivalence is based on pointer-equivalence NOT on a "deep equals".
      // Probably need a java-like "===" vs "==" to mean deep-equals.  You are
      // equals if your inputs are the same node, and you are unequals if your
      // input is 2 different NewNodes (or casts of NewNodes).  Otherwise you
      // have to do the runtime test.
      if( in(ARG_IDX)==in(ARG_IDX+1) ) return TypeInt.TRUE;
      Node nn1 = in(ARG_IDX).in(0), nn2 = in(ARG_IDX+1).in(0);
      if( nn1 instanceof NewNode &&
          nn2 instanceof NewNode &&
          nn1 != nn2 ) return TypeInt.FALSE;
      // Constants can only do nil-vs-not-nil, since e.g. two strings "abc" and
      // "abc" are equal constants in the type system but can be two different
      // string pointers.
      Type t1 = val(ARG_IDX);
      Type t2 = val(ARG_IDX+1);
      if( t1==Type.NIL || t1==Type.XNIL ) return vs_nil(t2,TypeInt.TRUE,TypeInt.FALSE);
      if( t2==Type.NIL || t2==Type.XNIL ) return vs_nil(t1,TypeInt.TRUE,TypeInt.FALSE);
      if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
      return TypeInt.BOOL;
    }
    @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
    static Type vs_nil( Type tx, Type t, Type f ) {
      if( tx==Type.NIL || tx==Type.XNIL ) return t;
      if( tx.above_center() ) return tx.isa(Type.NIL) ? TypeInt.BOOL.dual() : f;
      return tx.must_nil() ? TypeInt.BOOL : f;
    }
  }

  public static class NE_OOP extends PrimNode {
    public NE_OOP() { super("!=",TypeMemPtr.OOP_OOP,TypeInt.BOOL); }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      // Oop-equivalence is based on pointer-equivalence NOT on a "deep equals".
      // Probably need a java-like "===" vs "==" to mean deep-equals.  You are
      // equals if your inputs are the same node, and you are unequals if your
      // input is 2 different NewNodes (or casts of NewNodes).  Otherwise, you
      // have to do the runtime test.
      if( in(ARG_IDX)==in(ARG_IDX+1) ) return TypeInt.FALSE;
      Node nn1 = in(ARG_IDX).in(0), nn2 = in(ARG_IDX+1).in(0);
      if( nn1 instanceof NewNode &&
          nn2 instanceof NewNode &&
          nn1 != nn2 ) return TypeInt.TRUE;
      // Constants can only do nil-vs-not-nil, since e.g. two strings "abc" and
      // "abc" are equal constants in the type system but can be two different
      // string pointers.
      Type t1 = val(ARG_IDX);
      Type t2 = val(ARG_IDX+1);
      if( t1==Type.NIL || t1==Type.XNIL ) return EQ_OOP.vs_nil(t2,TypeInt.FALSE,TypeInt.TRUE);
      if( t2==Type.NIL || t2==Type.XNIL ) return EQ_OOP.vs_nil(t1,TypeInt.FALSE,TypeInt.TRUE);
      if( t1.above_center() || t2.above_center() ) return TypeInt.BOOL.dual();
      return TypeInt.BOOL;
    }
    @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
  }


  public static class Not extends PrimNode {
    // Rare function which takes a Scalar (works for both ints and ptrs)
    public Not() { super("!",TypeStruct.SCALAR1,TypeInt.BOOL); }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type t = val(ARG_IDX);
      if( t== Type.XNIL ||
          t== Type. NIL ||
          t== TypeInt.ZERO )
        return TypeInt.TRUE;
      if( t. may_nil() ) return TypeInt.BOOL.dual();
      if( t.must_nil() ) return TypeInt.BOOL;
      return Type.XNIL;           // Cannot be a nil, so return a nil
    }
    @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
  }

  public static class RandI64 extends PrimNode {
    public RandI64() { super("rand",TypeStruct.INT64,TypeInt.INT64); }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type t = val(ARG_IDX);
      if( t.above_center() ) return TypeInt.BOOL.dual();
      if( TypeInt.INT64.dual().isa(t) && t.isa(TypeInt.INT64) )
        return t.meet(TypeInt.FALSE);
      return t.oob(TypeInt.INT64);
    }
    @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
    // Rands have hidden internal state; 2 Rands are never equal
    @Override public boolean equals(Object o) { return this==o; }
  }

  // Classic '&&' short-circuit.  The RHS is a *Thunk* not a value.  Inlines
  // immediate into the operators' wrapper function, which in turn aggressively
  // inlines during parsing.
  public static class AndThen extends PrimNode {
    private static final TypeStruct ANDTHEN = TypeStruct.make2flds("pred",Type.SCALAR,"thunk",Type.SCALAR);
    // Takes a value on the LHS, and a THUNK on the RHS.
    public AndThen() { super("&&",ANDTHEN,Type.SCALAR); _thunk_rhs=true; }
    // Expect this to inline everytime
    @Override public Node ideal_grow() {
      if( _defs._len != ARG_IDX+2 ) return null; // Already did this
      try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
        Node ctl = in(CTL_IDX  );
        Node mem = in(MEM_IDX  );
        Node lhs = in(ARG_IDX  );
        Node rhs = in(ARG_IDX+1);
        // Expand to if/then/else
        Node iff = X.xform(new IfNode(ctl,lhs));
        Node fal = X.xform(new CProjNode(iff,0));
        Node tru = X.xform(new CProjNode(iff,1));
        // Call on true branch; if false do not call.
        Node cal = X.xform(new CallNode(true,_badargs,tru,mem,rhs));
        Node cep = X.xform(new CallEpiNode(cal,Env.DEFMEM));
        Node ccc = X.xform(new CProjNode(cep));
        Node memc= X.xform(new MProjNode(cep));
        Node rez = X.xform(new  ProjNode(cep,AA.REZ_IDX));
        // Region merging results
        Node reg = X.xform(new RegionNode(null,fal,ccc));
        Node phi = X.xform(new PhiNode(Type.SCALAR,null,reg,Node.con(Type.XNIL),rez ));
        Node phim= X.xform(new PhiNode(TypeMem.MEM,null,reg,mem,memc ));
        // Plug into self & trigger is_copy
        set_def(0,reg );
        set_def(1,phim);
        set_def(2,phi );
        pop();   pop();     // Remove args, trigger is_copy
        X.add(this);
        for( Node use : _uses ) X.add(use);
        return null;
      }
    }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      return TypeTuple.RET;
    }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==in(0) ) return TypeMem.ALIVE; // Control
      if( def==in(1) ) return TypeMem.ALLMEM; // Force maximal liveness, since will inline
      return TypeMem.LIVE_BOT; // Force maximal liveness, since will inline
    }
    @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
    //@Override public TV2 new_tvar(String alloc_site) { return TV2.make("Thunk",this,alloc_site); }
    @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
    @Override public Node is_copy(int idx) {
      return _defs._len==ARG_IDX+2 ? null : in(idx);
    }
  }

  // Classic '||' short-circuit.  The RHS is a *Thunk* not a value.  Inlines
  // immediate into the operators' wrapper function, which in turn aggressively
  // inlines during parsing.
  public static class OrElse extends PrimNode {
    private static final TypeStruct ORELSE = TypeStruct.make2flds("pred",Type.SCALAR,"thunk",Type.SCALAR);
    // Takes a value on the LHS, and a THUNK on the RHS.
    public OrElse() { super("||",ORELSE,Type.SCALAR); _thunk_rhs=true; }
    // Expect this to inline everytime
    @Override public Node ideal_grow() {
      if( _defs._len != ARG_IDX+2 ) return null; // Already did this
      try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
        Node ctl = in(CTL_IDX  );
        Node mem = in(MEM_IDX  );
        Node lhs = in(ARG_IDX  );
        Node rhs = in(ARG_IDX+1);
        // Expand to if/then/else
        Node iff = X.xform(new IfNode(ctl,lhs));
        Node fal = X.xform(new CProjNode(iff,0));
        Node tru = X.xform(new CProjNode(iff,1));
        // Call on false branch; if true do not call.
        Node cal = X.xform(new CallNode(true,_badargs,fal,mem,rhs));
        Node cep = X.xform(new CallEpiNode(cal,Env.DEFMEM));
        Node ccc = X.xform(new CProjNode(cep));
        Node memc= X.xform(new MProjNode(cep));
        Node rez = X.xform(new  ProjNode(cep,AA.REZ_IDX));
        // Region merging results
        Node reg = X.xform(new RegionNode(null,tru,ccc));
        Node phi = X.xform(new PhiNode(Type.SCALAR,null,reg,lhs,rez ));
        Node phim= X.xform(new PhiNode(TypeMem.MEM,null,reg,mem,memc ));
        // Plug into self & trigger is_copy
        set_def(0,reg );
        set_def(1,phim);
        set_def(2,phi );
        pop();   pop();     // Remove args, trigger is_copy
        X.add(this);
        for( Node use : _uses ) X.add(use);
        return null;
      }
    }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      return TypeTuple.RET;
    }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==in(0) ) return TypeMem.ALIVE; // Control
      if( def==in(1) ) return TypeMem.ALLMEM; // Force maximal liveness, since will inline
      return TypeMem.LIVE_BOT; // Force maximal liveness, since will inline
    }
    @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
    //@Override public TV2 new_tvar(String alloc_site) { return TV2.make("Thunk",this,alloc_site); }
    @Override public TypeInt apply( Type[] args ) { throw AA.unimpl(); }
    @Override public Node is_copy(int idx) {
      return _defs._len==ARG_IDX+2 ? null : in(idx);
    }
  }

}
