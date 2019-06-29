package com.cliffc.aa.node;

import com.cliffc.aa.AA;
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
  IntrinsicNode( String name, String[] args, TypeTuple targs, Type funret, Node... ns ) {
    super(OP_LIBCALL,ns);
    _name=name;
    _targs = targs;
    _funret = funret;           // Passed to the outer FunNode built in as_fun
    _args=args;
    _badargs=null;
    _all_type = TypeTuple.make(Type.CTRL,TypeMem.MEM,TypeMemPtr.OOP);
  }

  final static String[] ARGS1 = new String[]{"x"};
  
  @Override public Type all_type() { return _all_type; }
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
  // Takes in an unaliased piece of memory and Names it: basically sticks a
  // vtable name type in memory.  Unaliased, so the same memory cannot be
  // referred to without the Name.  Error if the memory cannot be proven
  // unaliased.  The Ideal call collapses the Name into the unaliased NewNode.
  public static EpilogNode convertTypeName( TypeObj from, TypeName to, Parse badargs, GVNGCM gvn ) {
    TypeFunPtr tf = TypeFunPtr.make_new(TypeTuple.make(TypeMemPtr.OOP),TypeMemPtr.OOP);
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,tf));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node mem = gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    Node ptr = gvn.xform(new ParmNode( 0,"ptr",fun,gvn.con(TypeMemPtr.OOP  ),null));
    Node cvt = gvn.xform(new ConvertPtrTypeName(from,to,badargs,mem,ptr));
    Node obj = gvn.xform(new ProjNode(cvt,0));
    Node nptr= gvn.xform(new ProjNode(cvt,1));
    Node mmem= gvn.xform(new MemMergeNode(mem,obj,nptr));
    return new EpilogNode(fun,mmem,nptr,rpc,fun,null);
  }

  // Names an unaliased memory.  Needs to collapse away, or else an error.
  static class ConvertPtrTypeName extends IntrinsicNode {
    private final HashMap<String,Type> _lex; // Unique lexical scope
    final TypeObj _from;
    final TypeName _to;
    ConvertPtrTypeName(TypeObj from, TypeName to, Parse badargs, Node mem, Node ptr) {
      super(to._name,ARGS1,TypeTuple.make(TypeMemPtr.STRUCT), TypeMemPtr.STRUCT, null, mem, ptr);
      _lex = to._lex;
      _badargs = badargs;
      _from = from;
      _to = to;
    }
    // Take in any struct alias or subclass thereof, with the given 'from'
    // type.  Most structs will NOT have this type.  The pointer passed in must
    // have this type to type-check.
    @Override public Type all_type() { return TypeTuple.make(TypeMem.MEM,TypeMemPtr.OOP); }

    @Override public Node ideal(GVNGCM gvn) {
      throw AA.unimpl();
    }
    
    @Override public Type value(GVNGCM gvn) {
      // Semantics are to extract a TypeObj from mem and ptr, and if there is
      // no aliasing, sharpen the TypeObj to a TypeName.  We can be correct and
      // conservative by doing nothing.
      Type mem = gvn.type(in(1)).bound(TypeMem.MEM);
      Type ptr = gvn.type(in(2)).bound(TypeMemPtr.OOP);
      return TypeTuple.make(mem,ptr);
    }
    @Override public String err(GVNGCM gvn) {
      //Type actual = gvn.type(in(1));
      //Type formal = _targs.at(0);
      //if( !actual.isa(formal) ) // Actual is not a formal
      //  return _badargs.typerr(actual,formal);
      //return null;
      throw AA.unimpl();
    }
  }
    
  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewNode.
  public static EpilogNode convertTypeNameStruct( TypeStruct from, TypeName to, Parse badargs, GVNGCM gvn ) {
    TypeFunPtr tf = TypeFunPtr.make_new(TypeTuple.make(TypeMemPtr.OOP),TypeMemPtr.OOP);
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,tf));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node memp= gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    Node[] ns= new Node[from._ts.length+1];
    // Add input edges to the NewNode
    for( int i=1; i<ns.length; i++ )
      ns[i] = gvn.xform(new ParmNode(i,from._flds[i],fun, gvn.con(from._ts[i]),null));
    Node nnn = gvn.xform(new NewNode(ns,to));
    Node obj = gvn.xform(new ProjNode(nnn,0)); // TypeStruct
    Node ptr = gvn.xform(new ProjNode(nnn,1)); // ptr-to-TypeStruct
    Node mmem= gvn.xform(new MemMergeNode(memp,obj,ptr));
    return new EpilogNode(fun,mmem,ptr,rpc,fun,null);
  }

}
