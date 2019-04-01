package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.node.MergeMemNode;

import java.util.HashMap;

// Known (intrinsic) library calls.  They typically have memory side effects,
// or else they would be a PrimNode instead.  Like PrimNodes they are wrapped
// in a Fun/Epilog but include memory effects.
public abstract class LibCallNode extends PrimNode {
  final TypeMemPtr _alias;
  LibCallNode( String name, String[] args, TypeTuple targs, Type ret, TypeMemPtr alias ) {
    super(OP_LIBCALL,name,args,targs,ret);
    _alias = alias;
  }
  
  public static LibCallNode[] LIBCALLS = new LibCallNode[] {
    new ConvertI64Str(TypeMemPtr.make(Type.new_alias())),
    new ConvertF64Str(TypeMemPtr.make(Type.new_alias())),
  };

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  @Override public EpilogNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this)); // Points to ScopeNode only
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun, gvn.con(TypeRPC.ALL_CALL),null));
    ParmNode mem = (ParmNode) gvn.xform(new ParmNode(-2,"mem",fun, gvn.con(TypeMem.MEM     ),null));
    add_def(null);              // Control for the primitive in slot 0
    add_def(mem );              // Memory  for the primitive in slot 1
    for( int i=0; i<_args.length; i++ ) // Args follow
      add_def(gvn.xform(new ParmNode(i,_args[i],fun, gvn.con(_targs.at(i)),null)));
    Node prim = gvn.xform(this);
    assert prim==this;
    Node mem_prim = gvn.xform(new MProjNode(this,0));
    Node val = gvn.xform(new ProjNode(this,1));
    Node mem2 = gvn.xform(new MergeMemNode(mem,mem_prim));
    return new EpilogNode(fun,mem2,val,rpc,fun,fun._tf.fidx(),null);
  }
  
  static class ConvertI64Str extends LibCallNode {
    ConvertI64Str(TypeMemPtr alias) {
      super("str",PrimNode.ARGS1,TypeTuple.INT64,
            // Return is a tuple of: (mem#alias:str, ptr#alias)
            TypeTuple.make(TypeMem.make(alias.get_alias(),TypeStr.STR),alias),
            alias);
    }
            
    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public TypeTuple apply( Type[] args ) {
      TypeMem mem = (TypeMem)args[1];
      Type val = args[2];
      TypeObj obj = mem.ld(_alias);
      TypeStr str = TypeStr.con(Long.toString(val.getl()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = mem.st(_alias,null,-1,obj2);
      return TypeTuple.make(res,_alias);
    }
    @Override public boolean is_lossy() { return false; }
  }
  
  static class ConvertF64Str extends LibCallNode {
    ConvertF64Str(TypeMemPtr alias) {
      super("str",PrimNode.ARGS1,TypeTuple.FLT64,
            // Return is a tuple of: (mem#alias:str, ptr#alias)
            TypeTuple.make(TypeMem.make(alias.get_alias(),TypeStr.STR),alias),
            alias);
    }
            
    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public TypeTuple apply( Type[] args ) {
      TypeMem mem = (TypeMem)args[1];
      Type val = args[2];
      TypeObj obj = mem.ld(_alias);
      TypeStr str = TypeStr.con(Double.toString(args[1].getd()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = mem.st(_alias,null,-1,obj2);
      return TypeTuple.make(res,_alias);
    }
    @Override public boolean is_lossy() { return false; }
  }

  
}
