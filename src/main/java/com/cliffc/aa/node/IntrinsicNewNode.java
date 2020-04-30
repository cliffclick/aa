package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Known (intrinsic) library calls.  They typically have memory side effects,
// or else they would be a PrimNode instead.  Like PrimNodes they are wrapped
// in a Fun/Epilog but include memory effects.
//
// These intrinsics take in memory of their alias# (same as a NewNode) and
// update it (like a Store would) producing a new instance of the same alias#.
// They also take in other arguments, and typically use them to define the
// contents of memory.  They output a TypeObj.
//
// The function wrapping these takes in all memory (like all functions do) and
// split out just the alias in question, and remerge with all memory before the
// epilog.
public abstract class IntrinsicNewNode extends Node {
  public final String _name;    // Unique library call name
  final NewStrNode _nstr;       // Main alias
  final TypeFunSig _sig;        // Arguments
  IntrinsicNewNode( String name, Type[] ts ) {
    super(OP_LIBCALL);
    _name = name;
    _nstr = new NewStrNode(TypeStr.STR,null,null);
    ts[0] = TypeFunPtr.NO_DISP; // No display
    _sig = TypeFunSig.make(TypeStruct.make_args(ts.length==2 ? TypeStruct.ARGS_X : TypeStruct.ARGS_XY,ts),TypeMemPtr.STRPTR);
  }
  public static IntrinsicNewNode[] INTRINSICS = new IntrinsicNewNode[] {
    new ConvertI64Str(),
    new ConvertF64Str(),
    new AddStrStr(),
  };
  @Override public String xstr() { return _name+"*"+_nstr._alias; }
  @Override public Type all_type() { return TypeStr.STR; }

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  public FunPtrNode as_fun( GVNGCM gvn ) {
    // Make NewStrNode to get alias
    NewStrNode nnn = gvn.init(_nstr).keep();
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this).add_def(Env.ALL_CTRL));
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node memp= gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM),null));
    gvn.add_work(memp);         // This may refine more later

    // Add input edges to the intrinsic
    add_def(null);              // Control for the primitive in slot 0
    add_def(memp);              // Memory  for the primitive in slot 1
    add_def(null);              // Closure for the primitive in slot 2
    for( int i=1; i<_sig.nargs(); i++ ) // Args follow, closure in formal 0
      add_def( gvn.xform(new ParmNode(i,_sig.fld(i),fun, gvn.con(_sig.arg(i).simple_ptr()),null)));
    Node rez = gvn.xform(this); // Returns a TypeObj
    // Fill in NewStrNode inputs, now that we have them.
    gvn.set_def_reg(nnn,0,fun);
    gvn.set_def_reg(nnn,1,rez);
    Node mem = gvn.xform(new OProjNode(nnn,0));
    Node ptr = gvn.xform(new  ProjNode(nnn,1));
    nnn.unhook();
    Node mmem= gvn.xform(new MemMergeNode(memp,mem,_nstr._alias));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,ptr,rpc,fun));
    mmem._live = mmem.live(gvn); // Refine initial memory
    return new FunPtrNode(ret,gvn.con(TypeFunPtr.NO_DISP));
  }

}

// --------------------------------------------------------------------------
class ConvertI64Str extends IntrinsicNewNode {
  ConvertI64Str() { super("str",TypeStruct.ts(null,TypeInt.INT64)); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(3));
    if( t.above_center() ) return all_type().dual();
    if( !t.is_con() || !(t instanceof TypeInt) ) return all_type();
    return TypeStr.make(false,Long.toString(t.getl()).intern());
  }
}

class ConvertF64Str extends IntrinsicNewNode {
  ConvertF64Str() { super("str",TypeStruct.ts(null,TypeFlt.FLT64)); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(3));
    if( t.above_center() ) return all_type().dual();
    if( !t.is_con() || !(t instanceof TypeFlt) ) return all_type();
    return TypeStr.make(false,Double.toString(t.getd()).intern());
  }
}

// String concat.  NIL values are treated "as-if" the empty string.
// If both arguments are NIL, NIL is returned.
// If one  argument  is  NIL, the other non-nil argument is returned.
// If neither argument is NIL, the two strings are concatenated into a new third string.
class AddStrStr extends IntrinsicNewNode {
  AddStrStr() { super("+",TypeStruct.ts(null,TypeMemPtr.STR0,TypeMemPtr.STR0)); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type m   = gvn.type(in(1));
    Type sp0 = gvn.type(in(3));
    Type sp1 = gvn.type(in(4));
    if( m.above_center() || sp0.above_center() || sp1.above_center() ) return all_type().dual();
    if( !(m instanceof TypeMem) ) return all_type();
    if( !sp0.isa(TypeMemPtr.STRPTR) || !sp1.isa(TypeMemPtr.STRPTR) ) return all_type();
    TypeMem mem = (TypeMem)m;
    if( sp0==Type.NIL ) return mem.ld((TypeMemPtr)sp1);
    if( sp1==Type.NIL ) return mem.ld((TypeMemPtr)sp0);
    Type s0 = mem.ld((TypeMemPtr)sp0);
    Type s1 = mem.ld((TypeMemPtr)sp1);
    if( !(s0 instanceof TypeStr) || !(s1 instanceof TypeStr) ) return all_type();
    TypeStr str0 = (TypeStr)s0;
    TypeStr str1 = (TypeStr)s1;
    if( !str0.is_con() || !str1.is_con() ) return all_type();
    return TypeStr.make(false,(str0.getstr()+str1.getstr()).intern());
  }
  @Override public byte op_prec() { return 5; }
}
