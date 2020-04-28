package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;
import org.jetbrains.annotations.NotNull;

// Function to wrap another type in a Name, which typically involves setting a
// vtable like field, i.e. memory updates.
// Names an unaliased memory.  Needs to collapse away, or else an error.
public class IntrinsicNode extends Node {
  public final TypeObj _tn;     // Named type
  Parse _badargs;               // Filled in when inlined in CallNode
  IntrinsicNode( TypeObj tn, Parse badargs, Node... ns ) {
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
  public static FunPtrNode convertTypeName( TypeObj tn, Parse badargs, GVNGCM gvn ) {
    // The incoming memory type is *exact* and does not have any extra fields.
    // The usual duck typing is "this-or-below", which allows and ignores extra
    // fields.  For Naming - which involves installing a v-table (or any other
    // RTTI) the type is exact at that moment.  Super-type constructors are
    // possible but here the type is exact.

    // This function call takes in and returns a plain ptr-to-object.
    // Only after folding together does the name become apparent.
    TypeFunPtr tf = TypeFunPtr.make_new(TypeStruct.make_args(TypeStruct.ts(TypeMemPtr.STRUCT,TypeStruct.NO_DISP_SIMPLE,TypeMemPtr.STRUCT)));
    FunNode fun = (FunNode) gvn.xform(new FunNode(tn._name,tf).add_def(Env.ALL_CTRL));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node mem = gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    Node ptr = gvn.xform(new ParmNode( 2,"ptr",fun,gvn.con(TypeMemPtr.OOP  ),null));
    Node cvt = gvn.xform(new IntrinsicNode(tn,badargs,fun,mem,ptr));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,cvt,ptr,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret,gvn.con(TypeStruct.NO_DISP_SIMPLE)));
  }

  @Override public Type all_type() { return TypeMem.MEM; }

  // If the input memory is unaliased, fold into the NewNode.
  // If this node does not fold away, the program is in error.
  @Override public Node ideal(GVNGCM gvn, int level) {
    if( mem() instanceof MemMergeNode ) {
      MemMergeNode mem = (MemMergeNode)mem();
      Node ptr = ptr();
      TypeMemPtr tptr = (TypeMemPtr)gvn.type(ptr);
      int alias = tptr._aliases.abit();
      Node opj = mem.alias2node(alias);
      if( alias > 0 &&          // Not a mixed set of aliases
          opj._uses._len==1 &&  // No unknown extra users
          opj instanceof OProjNode && ptr instanceof ProjNode &&
          opj.in(0)==ptr.in(0) && opj.in(0) instanceof NewNode ) {
        NewObjNode nnn = (NewObjNode)opj.in(0);
        // NewObjNode is well-typed and producing a pointer to memory with the
        // correct type?  Fold into the NewObjNode and remove this Convert.
        TypeTuple tnnn = (TypeTuple)gvn.type(nnn);
        Type actual = tnnn.at(0).sharpen(gvn.type(mem));
        Type formal = _tn.remove_name();
        if( actual.isa(formal) ) {
          TypeStruct tn = nnn._ts.make_from(_tn._name);
          nnn.set_name(tn,gvn);
          gvn.add_work(nnn);
          return new MemMergeNode(mem,opj,alias);
        }
      }
    }
    return null;
  }

  // Semantics are to extract a TypeObj from mem and ptr, and if there is no
  // aliasing, sharpen the TypeObj to a Type with a name.  We can be correct and
  // conservative by doing nothing.

  // The inputs are a TypeMem and a TypeMemPtr to an unnamed TypeObj.  If the
  // ptr is of the "from" type, we cast a Name to it and produce a pointer to
  // the "to" type, otherwise we get the most conservative "to" type.
  @Override public Type value(GVNGCM gvn) {
    Type mem = gvn.type(mem());
    Type ptr = gvn.type(ptr());
    if( !(mem instanceof TypeMem) ) return mem.above_center() ? TypeMem.XMEM : TypeMem.MEM ; // Inputs are confused
    if( !(ptr instanceof TypeMemPtr) ) return mem;       // Inputs are confused
    // Get the Obj from the pointer.
    int alias = ((TypeMemPtr)ptr)._aliases.abit();
    TypeObj obj = ((TypeMem)mem).ld((TypeMemPtr)ptr);
    TypeObj tn = (TypeObj)_tn.remove_name();
    if( !obj.isa(tn       ) ) return mem; // Inputs not correct from, and node is in-error
    if(  obj.isa(tn.dual()) ) return mem;
    // Wrap result in Name
    TypeObj rez = (TypeObj)obj.set_name(_tn._name);
    TypeMem rezmem = ((TypeMem)mem).st(alias,rez);
    return rezmem;
  }
  //
  @Override public boolean basic_liveness() { return false; }
  @Override public String err(GVNGCM gvn) {
    Type ptr = gvn.type(ptr());
    return _badargs.typerr(ptr,mem(),TypeMemPtr.make(BitsAlias.RECORD,_tn)); // Did not remove the aliasing
  }

  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewObjNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewObjNode.
  // Passed in a named TypeStruct, and the parent alias.
  public static FunPtrNode convertTypeNameStruct( TypeStruct to, int alias, GVNGCM gvn ) {
    assert to.has_name();
    assert Util.eq(to._flds[0],"^"); // Display already
    Type[] tsclr = TypeStruct.ts(to._ts.length);
    tsclr[0] = Type.XSCALAR;       // No display, but all other fields SCALAR
    NewObjNode nnn = new NewObjNode(false,alias,to.make_from(tsclr),null,gvn.con(Type.XNIL)).keep();
    // Tacky conversion from struct fields to function call args.
    Type[] ts = TypeAry.get(to._ts.length+1);
    ts[0] = TypeMemPtr.make(alias,to); // Return
    ts[1] = TypeStruct.NO_DISP_SIMPLE; // Display
    System.arraycopy(to._ts,1,ts,2,to._ts.length-1);
    TypeStruct args = TypeStruct.make_args(ts);
    TypeFunPtr tf = TypeFunPtr.make_new(args);
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,tf).add_def(Env.ALL_CTRL));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node memp= gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM),null));
    // Add input edges to the NewNode
    nnn.set_def(0,fun,gvn);     // Set control to function start
    for( int i=1; i<to._ts.length; i++ ) { // Display in 0, fields in 1+
      String argx = to._flds[i];
      if( TypeStruct.fldBot(argx) ) argx = null;
      nnn.add_def(gvn.xform(new ParmNode(i+1,argx,fun, gvn.con(to._ts[i].simple_ptr()),null)));
    }
    gvn.init(nnn);
    Node ptr = gvn.xform(new  ProjNode(nnn,1));
    Node obj = gvn.xform(new OProjNode(nnn,0));
    Node mmem= gvn.xform(new MemMergeNode(memp,obj,nnn.<NewObjNode>unhook()._alias));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,ptr,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret,gvn.con(TypeStruct.NO_DISP_SIMPLE)));
  }

}
