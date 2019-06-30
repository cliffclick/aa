package com.cliffc.aa.node;

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
  TypeMemPtr _ptr;              // private cache of the alias pointer
  IntrinsicNewNode( String name, String[] args, TypeTuple targs, Type funret, int alias ) {
    super(name,args,targs,funret);
    update_alias(alias);
  }
  private IntrinsicNewNode update_alias(int alias) {
    _alias = alias;
    _ptr = TypeMemPtr.make(alias);
    return this;
  }
  public static IntrinsicNewNode[] INTRINSICS = new IntrinsicNewNode[] {
    new ConvertI64Str(BitsAlias.I64),
    new ConvertF64Str(BitsAlias.F64)
  };
  // Clones during inlining all become unique new sites
  @Override IntrinsicNewNode copy(GVNGCM gvn) {
    IntrinsicNewNode nnn = (IntrinsicNewNode)super.copy(gvn);
    return nnn.update_alias(BitsAlias.new_alias(_alias,TypeStr.STR)); // Children alias classes
  }
  @Override public String xstr() { return _name+"_#"+_alias; }
  @Override public Type all_type() { return TypeStr.STR; }

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  public EpilogNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this,_funret));
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    ParmNode memp= (ParmNode) gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    // Add input edges to the intrinsic
    add_def(null);              // Control for the primitive in slot 0
    for( int i=0; i<_args.length; i++ ) // Args follow
      add_def(gvn.xform(new ParmNode(i,_args[i],fun, gvn.con(_targs.at(i)),null)));
    Node obj = gvn.xform(this); // Returns a TypeObj
    Node ptr = gvn.con(_ptr);
    Node mmem = gvn.xform(new MemMergeNode(memp,obj,ptr));
    return new EpilogNode(fun,mmem,ptr,rpc,fun,null);
  }
  
  // --------------------------------------------------------------------------
  static class ConvertI64Str extends IntrinsicNewNode {
    ConvertI64Str(int alias) { super("str",ARGS1,TypeTuple.INT64, TypeMemPtr.STRPTR,alias); }
    @Override public Type value(GVNGCM gvn) {
      Type t = gvn.type(in(1));
      if( t.above_center() ) return TypeStr.XSTR;
      if( !t.is_con() || !(t instanceof TypeInt) ) return TypeStr.STR;
      return TypeStr.con(Long.toString(t.getl()));
    }
  }
  
  static class ConvertF64Str extends IntrinsicNewNode {
    ConvertF64Str(int alias) { super("str",ARGS1,TypeTuple.FLT64, TypeMemPtr.STRPTR, alias); }
    @Override public Type value(GVNGCM gvn) {
      Type t = gvn.type(in(1));
      if( t.above_center() ) return TypeStr.XSTR;
      if( !t.is_con() || !(t instanceof TypeFlt) ) return TypeStr.STR;
      return TypeStr.con(Double.toString(t.getd()));
    }
  }
}
