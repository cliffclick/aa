package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import java.util.HashMap;

// Known (intrinsic) library calls.  They typically have memory side effects,
// or else they would be a PrimNode instead.  Like PrimNodes they are wrapped
// in a Fun/Epilog but include memory effects.
//
// These intrinsics take in memory of their alias# (same as a NewNode) and
// update it (like a Store would) producing a new instance of the same alias#.
// They also take in other arguments, and typically use them to define the
// contents of memory.  They output a TypeTuple[ctrl,mem,val] same as a
// CallNode, although the [ctrl] is always true and ignored.
//
// The function wrapping these takes in all memory (like all functions do) and
// split out just the alias in question, and remerge with all memory before the
// epilog.
public abstract class IntrinsicNode extends Node {
  public final String _name;    // Unique name (and program bits)
  final TypeTuple _targs;       // Argument types, 0-based
  final Type _funret;           // Primitive return type for outer as_fun, not memory effects
  final String[] _args;         // Handy string arg names; 0-based
  Parse _badargs;               // Filled in when inlined in CallNode
  TypeTuple _all_type;          // private cache of the CallNode-like return type
  IntrinsicNode( String name, String[] args, TypeTuple targs, Type funret ) {
    super(OP_LIBCALL);
    _name=name;
    _targs = targs;
    _funret = funret;           // Passed to the outer FunNode built in as_fun
    _args=args;
    _badargs=null;
    _all_type = TypeTuple.make(Type.CTRL,TypeMem.MEM,TypeMemPtr.OOP);
  }

  final static String[] ARGS1 = new String[]{"x"};
  
  @Override public Type all_type() { return _all_type; }

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  public EpilogNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this,_funret));
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    ParmNode memp= (ParmNode) gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    // Add input edges to the intrinsic
    add_def(null);              // Control for the primitive in slot 0
    add_def(memp);              // Aliased Memory in slot 1
    for( int i=0; i<_args.length; i++ ) // Args follow
      add_def(gvn.xform(new ParmNode(i,_args[i],fun, gvn.con(_targs.at(i)),null)));
    Node prim = gvn.xform(this); // Intrinsic returns a CallNode style tuple [ctrl,mem,ptr]
    Node mem2 = gvn.xform(new ProjNode(prim,1));
    Node val  = gvn.xform(new ProjNode(prim,2));
    Node merge= gvn.xform(new MemMergeNode(memp,mem2,_alias));
    return new EpilogNode(fun,merge,val,rpc,fun,null);
  }
  
  @Override public String xstr() { return _name; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  
  @Override public String err(GVNGCM gvn) {
    for( int i=0; i<_targs._ts.length; i++ ) {
      Type tactual = gvn.type(in(i+2));
      Type tformal = _targs._ts[i];
      if( !tactual.isa(tformal) )
        return _badargs==null ? "bad arguments" : _badargs.typerr(tactual,tformal);
    }
    return null;
  }

  // --------------------------------------------------------------------------
  public static IntrinsicNode convertTypeName( TypeObj from, TypeName to, Parse badargs ) {
    // Builds a function which takes in a TypeMemPtr.STRUCT and TypeMem[#REC,from]
    // (memory is constrained to match the 'from' type), and returns a
    // TypeMem[#REC,to].  The input is asserted to be sharper than a plain #REC
    // alias, in both iter() and opto() phases, and can never be nil.
    return new ConvertPtrTypeName(from,to,badargs);
  }
  static class ConvertPtrTypeName extends IntrinsicNode {
    private final HashMap<String,Type> _lex; // Unique lexical scope
    final TypeObj _from;
    final TypeName _to;
    ConvertPtrTypeName(TypeObj from, TypeName to, Parse badargs) {
      super(to._name,ARGS1,TypeTuple.make(TypeMemPtr.STRUCT), TypeMemPtr.STRUCT);
      _lex = to._lex;
      _badargs = badargs;
      _from = from;
      _to = to;
    }
    // Take in any struct alias or subclass thereof, with the given 'from'
    // type.  Most structs will NOT have this type.  The pointer passed in must
    // have this type to type-check.
    @Override public Type all_type() { return TypeTuple.make(Type.CTRL,TypeMem.MEM,TypeMemPtr.OOP0); }
    // No allocation, no new alias
    
    @Override public Type value(GVNGCM gvn) {
      Node nmem = _defs.at(1);
      Node nptr = _defs.at(2);
      Type tmem0= gvn.type(nmem);
      Type tptr0= gvn.type(nptr);
      if( !(tmem0 instanceof TypeMem) )
        return tmem0.above_center() ? all_type().dual() : all_type();
      if( !(tptr0 instanceof TypeMemPtr) )
        return tptr0.above_center() ? all_type().dual() : all_type();
      TypeMem tmem = (TypeMem)tmem0;
      TypeMemPtr tptr = (TypeMemPtr)tptr0;
      TypeObj ld = tmem.ld(tptr);
      Type ctrl = ld.above_center() ? Type.XCTRL : Type.CTRL;

      // ld can be high & fall to a from_dual, so use from_dual
      // ld can fall to from, so use ld
      // from can fall to ld, so use from
      // none-of-above, use +/-alltype
      TypeObj obj;
      if( ld.isa(_from.dual()) ) obj=(TypeObj)_from.dual();
      else if( ld.isa(_from) ) obj=ld;
      else if( _from.isa(ld) ) obj=_from;
      else {
        TypeTuple mem2 = TypeTuple.make(ctrl,TypeMem.MEM,tptr);
        return ld.above_center() ? mem2.dual() : mem2;
      }
      TypeName named_object = TypeName.make(_name,_lex,obj);
      TypeMem mem1 = tmem.st(tptr,named_object);
      return TypeTuple.make(ctrl,mem1,tptr);
    }
    @Override public String err(GVNGCM gvn) {
      Type actual = gvn.type(in(1));
      Type formal = _targs.at(0);
      if( !actual.isa(formal) ) // Actual is not a formal
        return _badargs.typerr(actual,formal);
      return null;
    }
  }
    
  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list
  public static EpilogNode convertTypeNameStruct( TypeStruct from, TypeName to, Parse badargs, GVNGCM gvn ) {
    ConvertPtrTypeName cptn = new ConvertPtrTypeName(from,to,badargs);
    EpilogNode epi = cptn.as_fun(gvn);
    // OLD NODE LAYOUT
    // Fun
    //  ParmMem, ParmRPC, ParmPtr
    //    CPTN
    //     MProj2, Proj
    //       MemMerge2(ParmMem,MProj2)
    //         Epilog
    assert epi.val().in(0)==cptn;
    FunNode fun = epi.fun();
    // Adjust the FunNode type to be the incoming split fields.
    fun._tf = TypeFunPtr.make(fun._tf.fidxs(),epi._args = TypeTuple.make(from._ts),fun._tf._ret);
    MemMergeNode mem2 = (MemMergeNode)epi.mem();
    ParmNode memp = (ParmNode)mem2.in(0);

    // Gather all args into a NewNode and make a struct
    Node[] flds = new Node[from._flds.length+1];
    for( int i=0; i<from._flds.length; i++ ) // Args follow
      flds[i+1] = gvn.xform(new ParmNode(i,from._flds[i],fun, gvn.con(from.at(i)),null));
    NewNode nn = (NewNode)gvn.xform(new NewNode(flds,from._flds));
    Node mn = gvn.xform(new MProjNode(nn,0));
    Node an = gvn.xform(new  ProjNode(nn,1));
    Node mem1= gvn.xform(new MemMergeNode(memp,mn,nn._alias));
    
    // Replace the single struct input from a parm with a NewNode from pieces-parts.
    assert ((ParmNode)cptn.in(2))._idx==0;
    gvn.set_def_reg(cptn,1,mem1);
    gvn.set_def_reg(cptn,2, an );
    gvn.set_def_reg(mem2,0,mem1);
    // NEW NODE LAYOUT
    // Fun
    //  ParmMem, ParmRPC, ParmX, ParmY, ParmZ
    //    NewNode
    //      MProj1, Proj
    //        MemMerge1(ParmMem,MProj1)
    //          CPTN
    //            MProj2, Proj
    //              MemMerge2(MemMerge1,MProj2)
    //                Epilog
    return epi;
  }

}
