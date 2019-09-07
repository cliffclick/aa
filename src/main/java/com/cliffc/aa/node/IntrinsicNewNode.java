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
// contents of memory.  They output a TypeTuple[ctrl,mem,val] same as a
// CallNode, although the [ctrl] is always true and ignored.
//
// The function wrapping these takes in all memory (like all functions do) and
// split out just the alias in question, and remerge with all memory before the
// epilog.
public abstract class IntrinsicNewNode extends IntrinsicNode {
  int _alias;                   // Alias class for new memory
  IntrinsicNewNode( String name, String[] args, TypeTuple targs, TypeMemPtr funret, int alias ) {
    super(name,args,targs,funret);
    update_alias(alias);
  }
  private IntrinsicNewNode update_alias(int alias) {
    _alias = alias;
    _funret = TypeMemPtr.make(alias,_funret._obj);
    return this;
  }
  public static IntrinsicNewNode[] INTRINSICS = new IntrinsicNewNode[] {
    new ConvertI64Str(BitsAlias.I64),
    new ConvertF64Str(BitsAlias.F64)
  };
  // Clones during inlining all become unique new sites
  @Override IntrinsicNewNode copy(GVNGCM gvn) {
    IntrinsicNewNode nnn = (IntrinsicNewNode)super.copy(gvn);
    return nnn.update_alias(BitsAlias.new_alias(_alias)); // Children alias classes
  }
  @Override public String xstr() { return _name+"*"+_alias; }
  @Override public Type all_type() { return _funret; }

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  public FunPtrNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this,_funret).add_def(Env.ALL_CTRL));
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    ParmNode memp= (ParmNode) gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    // Add input edges to the intrinsic
    add_def(null);              // Control for the primitive in slot 0
    add_def(memp);              // Control for the memory    in slot 1
    for( int i=0; i<_args.length; i++ ) // Args follow
      add_def(gvn.xform(new ParmNode(i,_args[i],fun, gvn.con(_targs.at(i)),null)));
    Node ptr = gvn.xform(this); // Returns a TypeMemPtr to a TypeObj
    Node mmem = gvn.xform(new MemMergeNode(memp,ptr));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,ptr,rpc,fun));
    return new FunPtrNode(ret);
  }
  
  // --------------------------------------------------------------------------
  static class ConvertI64Str extends IntrinsicNewNode {
    ConvertI64Str(int alias) { super("str",ARGS1,TypeTuple.INT64, TypeMemPtr.STRPTR,alias); }
    @Override public Type value(GVNGCM gvn) {
      Type t = gvn.type(in(2));
      if( t.above_center() ) return _funret.dual();
      if( !t.is_con() || !(t instanceof TypeInt) ) return _funret;
      return TypeMemPtr.make(_alias,TypeStr.con(Long.toString(t.getl())));
    }
  }
  
  static class ConvertF64Str extends IntrinsicNewNode {
    ConvertF64Str(int alias) { super("str",ARGS1,TypeTuple.FLT64, TypeMemPtr.STRPTR, alias); }
    @Override public Type value(GVNGCM gvn) {
      Type t = gvn.type(in(2));
      if( t.above_center() ) return _funret.dual();
      if( !t.is_con() || !(t instanceof TypeFlt) ) return _funret;
      return TypeMemPtr.make(_alias,TypeStr.con(Double.toString(t.getd())));
    }
  }
}
