package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Known (intrinsic) library calls.  They typically have memory side effects,
// or else they would be a PrimNode instead.  Like PrimNodes they are wrapped
// in a Fun/Epilog but include memory effects.
public abstract class LibCallNode extends PrimNode {
  TypeTree _alias;                   // Alias class for new memory
  LibCallNode( String name, String[] args, TypeTuple targs, Type ret, TypeTree alias ) {
    super(OP_LIBCALL,name,args,targs,ret);
    _alias = alias;
  }

  public static LibCallNode[] LIBCALLS = new LibCallNode[] {
    new ConvertI64Str(BitsAlias.new_string()),
    new ConvertF64Str(BitsAlias.new_string())
  };

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  @Override public EpilogNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this,((TypeTuple)_ret).at(1))); // Points to ScopeNode only
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
  
  // Clones during inlining all become unique new sites
  @Override LibCallNode copy(GVNGCM gvn) {
    LibCallNode nnn = super.copy(gvn);
    TypeTree par = _alias;      // Parent alias class
        _alias = BitsAlias.new_alias(par); // Children alias classes
    nnn._alias = BitsAlias.new_alias(par); // Children alias classes
    return nnn;
  }
  @Override public String xstr() { return _name+"::#"+_alias._idx; }
  
  @Override public String err(GVNGCM gvn) {
    for( int i=0; i<_targs._ts.length; i++ ) {
      Type tactual = gvn.type(in(i+2));
      Type tformal = _targs._ts[i];
      if( !tactual.isa(tformal) )
        return _badargs==null ? "bad arguments" : _badargs.typerr(tactual,tformal);
    }
    return null;
  }

  static class ConvertI64Str extends LibCallNode {
    ConvertI64Str(TypeTree alias) {
      super("str",PrimNode.ARGS1,TypeTuple.INT64,
            // Return is a tuple of: (mem#alias:str, ptr#alias)
            TypeTuple.make(TypeMem.make(alias._idx,TypeStr.STR),TypeMemPtr.make(alias._idx)),
            alias);
    }
            
    // Library calls update memory.  These calls have the default boot-time
    // memory inputs and outputs.
    @Override TypeMem argmem() { return TypeMem.MEM; }
    @Override TypeMem retmem() { return TypeMem.make(_alias._idx,TypeStr.STR); }
    @Override public Type startype() {
      return TypeTuple.make(TypeMem.make(_alias._idx,TypeStr.XSTR), TypeMemPtr.make(_alias._idx).dual());
    }
  
    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public TypeTuple apply( Type[] args ) {
      TypeMem mem = (TypeMem)args[1];
      TypeMemPtr alias = TypeMemPtr.make(_alias._idx);
      Type val = args[2];
      TypeObj obj = mem.ld(alias);
      TypeStr str = TypeStr.con(Long.toString(val.getl()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = mem.st(alias,null,-1,obj2);
      return TypeTuple.make(res,alias);
    }
    @Override public boolean is_lossy() { return false; }
  }
  
  static class ConvertF64Str extends LibCallNode {
    ConvertF64Str(TypeTree alias) {
      super("str",PrimNode.ARGS1,TypeTuple.FLT64,
            // Return is a tuple of: (mem#alias:str, ptr#alias)
            TypeTuple.make(TypeMem.make(alias._idx,TypeStr.STR),TypeMemPtr.make(alias._idx)),
            alias);
    }
            
    // Library calls update memory.  These calls have the default boot-time
    // memory inputs and outputs.
    @Override TypeMem argmem() { return TypeMem.XMEM; }
    @Override TypeMem retmem() { return TypeMem.make(_alias._idx,TypeStr.STR); }
    @Override public Type startype() {
      return TypeTuple.make(TypeMem.make(_alias._idx,TypeStr.XSTR), TypeMemPtr.make(_alias._idx).dual());
    }
    
    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public Type value(GVNGCM gvn) {
      // If the meet with _targs.dual stays above center for all inputs, then we
      // return _ret.dual, the highest allowed result; if all inputs are
      // constants we constant fold; else some input is low so we return _ret,
      // the lowest possible result.
      boolean is_con = true;
      for( int i=2; i<_defs._len; i++ ) {
        Type t = _targs.at(i-2).dual().meet(gvn.type(in(i)));
        if( t.above_center() ) is_con = false; // Not a constant
        else if( !t.is_con() ) return _ret;    // Some input is too low
      }
      if( !is_con ) return _ret.dual(); // Some inputs above center and none are low
      
      // Conversion to String allocates memory - so return a new pointer
      // aliased to a hidden String allocation site.  The memory returned is
      // read-only (and can be shared).
      TypeMem mem = (TypeMem)gvn.type(in(1));
      TypeObj obj = mem.at(_alias._idx);  // Prior memory contents at this alias
      Type val = gvn.type(in(2));    // Known constant
      TypeStr str = TypeStr.con(Double.toString(val.getd()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = TypeMem.make(_alias._idx,obj2);
      return TypeTuple.make(res,TypeMemPtr.make(_alias._idx));
    }
    @Override public TypeTuple apply( Type[] args ) { throw com.cliffc.aa.AA.unimpl(); }
    @Override public boolean is_lossy() { return false; }
  }
}
