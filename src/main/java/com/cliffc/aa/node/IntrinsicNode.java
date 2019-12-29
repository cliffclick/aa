package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Function to wrap another type in a Name, which typically involves setting a
// vtable like field, i.e. memory updates.
// Names an unaliased memory.  Needs to collapse away, or else an error.
public class IntrinsicNode extends Node {
  public final TypeName _tn;    // Unique name
  Parse _badargs;               // Filled in when inlined in CallNode
  IntrinsicNode( TypeName tn, Parse badargs, Node... ns ) {
    super(OP_NAME,ns);
    _tn=tn;
    _badargs=badargs;
  }

  @Override public String xstr() { return _tn._name; }
  Node mem() { return in(1); }
  Node ptr() { return in(2); }

  // --------------------------------------------------------------------------
  // Takes in an unaliased piece of memory and Names it: basically sticks a
  // vtable name type in memory.  Unaliased, so the same memory cannot be
  // referred to without the Name.  Error if the memory cannot be proven
  // unaliased.  The Ideal call collapses the Name into the unaliased NewNode.
  public static FunPtrNode convertTypeName( TypeName tn, Parse badargs, GVNGCM gvn ) {
    // The incoming memory type is *exact* and does not have any extra fields.
    // The usual duck typing is "this-or-below", which allows and ignores extra
    // fields.  For Naming - which involves installing a v-table (or any other
    // RTTI) the type is exact at that moment.  Super-type constructors are
    // possible but here the type is exact.

    // This function call takes in and returns a plain ptr-to-object.
    // Only after folding together does the name become apparent.
    TypeFunPtr tf = TypeFunPtr.make_new(TypeStruct.make(TypeMemPtr.STRUCT),TypeMemPtr.STRUCT);
    FunNode fun = (FunNode) gvn.xform(new FunNode(tn._name,tf).add_def(Env.ALL_CTRL));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL ),null));
    Node mem = gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM      ),null));
    Node ptr = gvn.xform(new ParmNode( 0,"ptr",fun,gvn.con(TypeMemPtr.STRUCT),null));
    Node cvt = gvn.xform(new IntrinsicNode(tn,badargs,fun,mem,ptr));
    Node mmem= gvn.xform(new MemMergeNode(mem,cvt,BitsAlias.REC));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,cvt,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret));
  }

  @Override public TypeName all_type() { return _tn; }

  // If the input memory is unaliased, fold into the NewNode.
  // If this node does not fold away, the program is in error.
  @Override public Node ideal(GVNGCM gvn) {
    if( mem() instanceof MemMergeNode ) {
      MemMergeNode mem = (MemMergeNode)mem();
      Node ptr = ptr();
      TypeMemPtr tptr = (TypeMemPtr)gvn.type(ptr);
      Node opj = mem.alias2node(tptr._aliases.abit());
      if( opj instanceof OProjNode && ptr instanceof ProjNode &&
          opj.in(0)==ptr.in(0) && opj.in(0) instanceof NewNode ) {
        NewObjNode nnn = (NewObjNode)opj.in(0);
        // NewObjNode is well-typed and producing a pointer to memory with the
        // correct type?  Fold into the NewObjNode and remove this Convert.
        TypeTuple tnnn = (TypeTuple)gvn.type(nnn);
        //if( tnnn.at(1).isa(_targs.at(0)) ) {
        //  nnn.set_name(gvn,all_type());
        //  gvn.add_work(nnn);
        //  return ptr;
        //}
        throw AA.unimpl();
      }
    }
    return null;
  }

  // Semantics are to extract a TypeObj from mem and ptr, and if there is no
  // aliasing, sharpen the TypeObj to a TypeName.  We can be correct and
  // conservative by doing nothing.

  // The inputs are a TypeMem and a TypeMemPtr to an unnamed TypeObj.  If the
  // ptr is of the "from" type, we cast a Name to it and produce a pointer to
  // the "to" type, otherwise we get the most conservative "to" type.
  @Override public Type value(GVNGCM gvn) {
    Type mem = gvn.type(mem());
    Type ptr = gvn.type(ptr());
    if( !(mem instanceof TypeMem && ptr instanceof TypeMemPtr) )
      return _tn;               // Inputs are confused
    // Get the Obj from the pointer.  We are renaming it in-place, basically
    // changing the vtable.  We need the l-value.
    TypeObj obj = ((TypeMem)mem).ld((TypeMemPtr)ptr);
    if( !obj.isa(_tn._t       ) ) return _tn       ; // Inputs not correct from, and node is in-error
    if(  obj.isa(_tn._t.dual()) ) return _tn.dual();
    // Obj needs to share a common name hierarchy (same Name-depth) as 'from'
    int fd = _tn._depth;
    int od = obj instanceof TypeName ? ((TypeName)obj)._depth : -1;
    if( fd-1 != od ) return obj.above_center() ? _tn.dual() : _tn; // Name-depth does not match, node is in-error
    //
    //// Wrap result in 1 layer of Name
    //return tname.make(obj);
    throw AA.unimpl();
  }
  @Override public String err(GVNGCM gvn) {
    Type ptr = gvn.type(ptr());
    return _badargs.typerr(ptr,_tn); // Did not remove the aliasing
  }

  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewObjNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewObjNode.
  public static FunPtrNode convertTypeNameStruct( TypeName to, GVNGCM gvn ) {
    TypeStruct from = (TypeStruct)to._t;
    NewObjNode nnn = new NewObjNode(false,null);
    TypeMemPtr tmp = TypeMemPtr.make(nnn._alias);
    TypeFunPtr tf = TypeFunPtr.make_new(from,tmp);
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,tf).add_def(Env.ALL_CTRL));
    nnn.set_def(0,fun,gvn);     // Set control to function start
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node memp= gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    // Add input edges to the NewNode
    nnn._ts = from;             // Bulk set fields and types
    nnn._name = to;             // Bulk set fields and types
    for( int i=0; i<from._ts.length; i++ ) {
      String argx = from._flds[i];
      if( TypeStruct.fldBot(argx) ) argx = null;
      nnn.add_def(gvn.xform(new ParmNode(i,argx,fun, gvn.con(from._ts[i]),null)));
    }
    gvn.init(nnn);
    Node ptr = gvn.xform(new  ProjNode(nnn,1));
    Node obj = gvn.xform(new OProjNode(nnn,0));
    Node mmem= gvn.xform(new MemMergeNode(memp,obj,nnn._alias));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,ptr,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret));
  }

}
