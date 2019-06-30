package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

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
  IntrinsicNode( String name, String[] args, TypeTuple targs, Type funret, Node... ns ) {
    super(OP_LIBCALL,ns);
    _name=name;
    _targs = targs;
    _funret = funret;           // Passed to the outer FunNode built in as_fun
    _args=args;
    _badargs=null;
  }

  final static String[] ARGS1 = new String[]{"x"};
  
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
    Node mmem= gvn.xform(new MemMergeNode(mem,cvt,ptr));
    return new EpilogNode(fun,mmem,ptr,rpc,fun,null);
  }

  // Names an unaliased memory.  Needs to collapse away, or else an error.
  static class ConvertPtrTypeName extends IntrinsicNode {
    final TypeObj _from;
    final TypeName _to;
    ConvertPtrTypeName(TypeObj from, TypeName to, Parse badargs, Node mem, Node ptr) {
      super(to._name,ARGS1,TypeTuple.make(TypeMemPtr.OOP), TypeMemPtr.OOP, null, mem, ptr);
      _badargs = badargs;
      _from = from;
      _to = to;
    }
    Node mem() { return in(1); }
    Node ptr() { return in(2); }
    // Take in any struct alias or subclass thereof, with the given 'from'
    // type.  Most structs will NOT have this type.  The pointer passed in must
    // have this type to type-check.
    @Override public Type all_type() { return _to; }

    @Override public Node ideal(GVNGCM gvn) {
      if( mem() instanceof MemMergeNode ) {
        MemMergeNode mem = (MemMergeNode)mem();
        NewNode nnn = mem.exact(ptr());
        if( nnn != null && nnn._ts.isa(_from) ) {
          throw AA.unimpl();
        }
      }
      return null;
    }
    
    @Override public Type value(GVNGCM gvn) {
      // Semantics are to extract a TypeObj from mem and ptr, and if there is
      // no aliasing, sharpen the TypeObj to a TypeName.  We can be correct and
      // conservative by doing nothing.
      Type mem = gvn.type(mem());
      Type ptr = gvn.type(ptr());
      if( !(mem instanceof TypeMem && ptr instanceof TypeMemPtr) )
        return _to;             // Inputs are confused
      Type obj = ((TypeMem)mem).ld((TypeMemPtr)ptr);
      if( !obj.isa(_from) )     // Inputs not correct _from
        return _to;             // 
      return _to.make(obj).bound(_to);     // Wrap a Name around the Obj
    }
    @Override public String err(GVNGCM gvn) {
      Type mem = gvn.type(mem());
      Type ptr = gvn.type(ptr());
      Type actual = ((TypeMem)mem).ld((TypeMemPtr)ptr);
      if( !actual.isa(_from) )
        return _badargs.typerr(actual,_from);
      throw AA.unimpl();        // Did not remove the aliasing
    }
  }
    
  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewNode.
  public static EpilogNode convertTypeNameStruct( TypeStruct from, TypeName to, Parse badargs, GVNGCM gvn ) {
    TypeFunPtr tf = TypeFunPtr.make_new(TypeTuple.make(from._ts),TypeMemPtr.OOP);
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,tf));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node memp= gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    Node[] ns= new Node[from._ts.length+1];
    // Add input edges to the NewNode
    for( int i=0; i<from._ts.length; i++ )
      ns[i+1] = gvn.xform(new ParmNode(i,from._flds[i],fun, gvn.con(from._ts[i]),null));
    Node nnn = gvn.xform(new NewNode(ns,to));
    Node obj = gvn.xform(new OProjNode(nnn,0)); // TypeStruct
    Node ptr = gvn.xform(new  ProjNode(nnn,1)); // ptr-to-TypeStruct
    ptr.add_def(ptr);                           // Add self-hook to prevent deletion
    Node mmem= gvn.xform(new MemMergeNode(memp,obj,ptr));
    ptr.pop();                  // Remove self-hook
    return new EpilogNode(fun,mmem,ptr,rpc,fun,null);
  }

}
