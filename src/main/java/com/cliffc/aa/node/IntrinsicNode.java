package com.cliffc.aa.node;

import com.cliffc.aa.Env;
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
  TypeMemPtr _funret;   // Primitive return type for outer as_fun, not memory effects
  final String[] _args;         // Handy string arg names; 0-based
  Parse _badargs;               // Filled in when inlined in CallNode
  IntrinsicNode( String name, String[] args, TypeTuple targs, TypeMemPtr funret, Node... ns ) {
    super(OP_LIBCALL,ns);
    _name=name;
    _targs = targs;
    _funret = funret;           // Passed to the outer FunNode built in as_fun
    _args=args;
    _badargs=null;
  }

  final static String[] ARGS1 = new String[]{"x"};
  final static String[] ARGS2 = new String[]{"x","y"};

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
  public static FunPtrNode convertTypeName( TypeObj from, TypeName to, Parse badargs, GVNGCM gvn ) {
    // The incoming memory type is *exact* and does not have any extra fields.
    // The usual duck typing is "this-or-below", which allows and ignores extra
    // fields.  For Naming - which involves installing a v-table (or any other
    // RTTI) the type is exact at that moment.  Super-type constructors are
    // possible but here the type is exact.

    // So TypeFunPtr takes in a ptr-to-from and returns a ptr-to-to.
    TypeMemPtr from_ptr = TypeMemPtr.make(BitsAlias.REC,from);
    TypeMemPtr to_ptr   = TypeMemPtr.make(BitsAlias.REC,to  );
    TypeFunPtr tf = TypeFunPtr.make_new(TypeTuple.make(from_ptr),to_ptr);
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,tf).add_def(Env.ALL_CTRL));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node mem = gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    Node ptr = gvn.xform(new ParmNode( 0,"ptr",fun,gvn.con(from_ptr        ),null));
    Node cvt = gvn.xform(new ConvertPtrTypeName(to._name,from_ptr,to_ptr,badargs,mem,ptr));
    Node mmem= gvn.xform(new MemMergeNode(mem,cvt));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,cvt,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret));
  }

  // Names an unaliased memory.  Needs to collapse away, or else an error.
  static class ConvertPtrTypeName extends IntrinsicNode {
    ConvertPtrTypeName(String name, TypeMemPtr from_ptr, TypeMemPtr to_ptr, Parse badargs, Node mem, Node ptr) {
      super(name,ARGS1,TypeTuple.make(from_ptr), to_ptr, null, mem, ptr);
      _badargs = badargs;
    }
    Node mem() { return in(1); }
    Node ptr() { return in(2); }
    // Take in any struct alias or subclass thereof, with the given 'from'
    // type.  Most structs will NOT have this type.  The pointer passed in must
    // have this type to type-check.
    @Override public TypeObj all_type() { return _funret._obj; }

    // If the input memory is unaliased, fold into the NewNode.
    // If this node does not fold away, the program is in error.
    @Override public Node ideal(GVNGCM gvn) {
      if( mem() instanceof MemMergeNode ) {
        MemMergeNode mem = (MemMergeNode)mem();
        NewNode nnn = mem.exact(ptr());
        if( mem._uses._len == 2 && // Use is 'this' and the MemMerge just after 'this'
            nnn != null ) {     // Un-aliased NewNode
          // NewNode is well-typed and producing a pointer to memory with the
          // correct type?  Fold into the NewNode and remove this Convert.
          TypeTuple tnnn = (TypeTuple)gvn.type(nnn);
          if( tnnn.at(1).isa(_targs.at(0)) ) {
            nnn.set_name(gvn,(TypeName)_funret._obj);
            gvn.add_work(nnn);
            return nnn;
          }
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
      TypeMemPtr from = (TypeMemPtr)_targs._ts[0];
      TypeMemPtr to   =             _funret;
      TypeName tname  = (TypeName  )to._obj;
      Type mem = gvn.type(mem());
      Type ptr = gvn.type(ptr());
      if( !(mem instanceof TypeMem && ptr instanceof TypeMemPtr) )
        return tname;            // Inputs are confused
      // Get the Obj from the pointer.  We are renaming it in-place, basically
      // changing the vtable.  We need the l-value.
      TypeObj obj = ((TypeMem)mem).ld((TypeMemPtr)ptr);
      if( !obj.isa(from._obj) ) return tname; // Inputs not correct from, and node is in-error
      if( obj.isa(from._obj.dual()) ) return tname.dual();
      // Obj needs to share a common name hierarchy (same Name-depth) as 'from'
      int fd = from._obj instanceof TypeName ? ((TypeName)from._obj)._depth : -1;
      int od =       obj instanceof TypeName ? ((TypeName)      obj)._depth : -1;
      if( fd != od ) return obj.above_center() ? tname.dual() : tname; // Name-depth does not match, node is in-error
      // 'ptr' might be 'dull' during iter() while 'mem' gets sharp first.
      // Then the 'ld' can correctly return a TypeStruct with a sharper '_news'
      // than 'ptr'.  Bail out and wait for ptr to sharpen up.
      TypeMemPtr tptr = (TypeMemPtr)ptr;
      if( obj instanceof TypeStruct && tptr._aliases != ((TypeStruct)obj)._news )
        return obj.above_center() ? tname.dual() : tname; // Name-depth does not match, node is in-error

      // Wrap result in 1 layer of Name
      return tname.make(obj);
    }
    @Override public String err(GVNGCM gvn) {
      Type ptr = gvn.type(ptr());
      return _badargs.typerr(ptr,_targs.at(0)); // Did not remove the aliasing
    }
  }

  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewNode.
  public static FunPtrNode convertTypeNameStruct( TypeStruct from, TypeName to, GVNGCM gvn ) {
    NewNode nnn = new NewNode();
    nnn.set_name(gvn,to);
    TypeFunPtr tf = TypeFunPtr.make_new(TypeTuple.make(from._ts),nnn.ptr());
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,tf).add_def(Env.ALL_CTRL));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node memp= gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    // Add input edges to the NewNode
    for( int i=0; i<from._ts.length; i++ ) {
      String argx = from._flds[i];
      String argy = argx.equals(".") ? "arg"+i : argx;
      Type t = from._ts[i];
      boolean mutable = from._finals[i]==TypeStruct.frw();
      nnn.add_fld(argy,t,gvn.xform(new ParmNode(i,argy,fun, gvn.con(t),null)),mutable);
    }
    Node nnn2 = gvn.xform(nnn);
    Node obj = gvn.xform(new OProjNode(nnn2,0));
    Node ptr = gvn.xform(new  ProjNode(nnn2,1));
    Node mmem= gvn.xform(new MemMergeNode(memp,obj));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,ptr,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret));
  }

}
