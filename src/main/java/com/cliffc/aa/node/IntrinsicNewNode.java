package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

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
  IntrinsicNewNode( String name, String[] args, TypeTuple targs, int alias ) {
    super(name,args,targs,null);
    update_alias(alias);
  }
  private IntrinsicNewNode update_alias(int alias) {
    _alias = alias;
    _funret = TypeMemPtr.make(alias,TypeStr.make(false,null,BitsAlias.make0(alias)));
    return this;
  }
  public static IntrinsicNewNode[] INTRINSICS = new IntrinsicNewNode[] {
    new ConvertI64Str(),
    new ConvertF64Str(),
    new AddStrStr(),
  };
  private BitsAlias alias_bits() { return _funret._obj._news; }
  // Clones during inlining all become unique new sites
  @Override @NotNull IntrinsicNewNode copy( boolean copy_edges, GVNGCM gvn) {
    IntrinsicNewNode nnn = (IntrinsicNewNode)super.copy(copy_edges, gvn);
    return nnn.update_alias(BitsAlias.new_alias(_alias)); // Children alias classes
  }
  @Override public String xstr() { return _name+"*"+_alias; }
  @Override public Type all_type() { return TypeTuple.make(_funret._obj,_funret); }

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  public FunPtrNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this,_funret).add_def(Env.ALL_CTRL));
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    ParmNode memp= (ParmNode) gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    // Add input edges to the intrinsic
    add_def(null);              // Control for the primitive in slot 0
    add_def(memp);              // Memory  for the primitive in slot 1
    for( int i=0; i<_args.length; i++ ) // Args follow
      add_def( gvn.xform(new ParmNode(i,_args[i],fun, gvn.con(_targs.at(i)),null)));
    Node rez = gvn.xform(this); // Returns a Tuple(mem,ptr)
    Node mem = gvn.xform(new OProjNode(rez,0));
    Node ptr = gvn.xform(new  ProjNode(rez,1));
    Node mmem= gvn.xform(new MemMergeNode(memp,mem,_alias));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,ptr,rpc,fun));
    return new FunPtrNode(ret);
  }

  // --------------------------------------------------------------------------
  static class ConvertI64Str extends IntrinsicNewNode {
    ConvertI64Str() { super("str",ARGS1,TypeTuple.INT64,BitsAlias.I64); }
    @Override public Type value(GVNGCM gvn) {
      Type t = gvn.type(in(2));
      if( t.above_center() ) return all_type().dual();
      if( !t.is_con() || !(t instanceof TypeInt) ) return all_type();
      TypeStr str = TypeStr.make(false,Long.toString(t.getl()).intern(),alias_bits());
      return TypeTuple.make(str,TypeMemPtr.make(_alias,str));
    }
  }

  static class ConvertF64Str extends IntrinsicNewNode {
    ConvertF64Str() { super("str",ARGS1,TypeTuple.FLT64, BitsAlias.F64); }
    @Override public Type value(GVNGCM gvn) {
      Type t = gvn.type(in(2));
      if( t.above_center() ) return all_type().dual();
      if( !t.is_con() || !(t instanceof TypeFlt) ) return all_type();
      TypeStr str = TypeStr.make(false,Double.toString(t.getd()).intern(),alias_bits());
      return TypeTuple.make(str,TypeMemPtr.make(_alias,str));
    }
  }

  // String concat.  NIL values are treated "as-if" the empty string.
  // If both arguments are NIL, NIL is returned.
  // If one  argument  is  NIL, the other non-nil argument is returned.
  // If neither argument is NIL, the two strings are concatenated into a new third string.
  static class AddStrStr extends IntrinsicNewNode {
    // TODO BUG: Default behavior stomps memory type to [mem] when not inlined,
    // and not resolved.  GCP then cannot keep the correct memory type.
    // Probably need Unresolved to disallow memory updates in e.g. CallEpiNode
    // across all Prims.
    //
    // TODO: Confirm unknown-caller in GCP on Prims is dead path; so when doing
    // Unresolved, all prims "look dead", including memory state.  Keep them
    // dead until resolving or not.
    //
    AddStrStr() { super("+",ARGS2,TypeTuple.STR_STR, BitsAlias.STR_STR); }
    @Override public Type value(GVNGCM gvn) {
      Type m   = gvn.type(in(1));
      Type sp0 = gvn.type(in(2));
      Type sp1 = gvn.type(in(3));
      if( m.above_center() || sp0.above_center() || sp1.above_center() ) return all_type().dual();
      if( !(m instanceof TypeMem) ) return all_type();
      if( sp0==Type.NIL ) return TypeTuple.make(((TypeMemPtr)sp1)._obj,sp1);
      if( sp1==Type.NIL ) return TypeTuple.make(((TypeMemPtr)sp0)._obj,sp1);
      if( !sp0.isa(TypeMemPtr.STRPTR) || !sp1.isa(TypeMemPtr.STRPTR) ) return all_type();
      TypeMem mem = (TypeMem)m;
      Type s0 = mem.ld((TypeMemPtr)sp0);
      Type s1 = mem.ld((TypeMemPtr)sp1);
      if( !(s0 instanceof TypeStr) || !(s1 instanceof TypeStr) ) return all_type();
      TypeStr str0 = (TypeStr)s0;
      TypeStr str1 = (TypeStr)s1;
      if( !str0.is_con() || !str1.is_con() ) return all_type();
      TypeStr str = TypeStr.make(false,(str0.getstr()+str1.getstr()).intern(),alias_bits());
      return TypeTuple.make(str,TypeMemPtr.make(_alias,str));
    }
    @Override public byte op_prec() { return 5; }
  }
}
