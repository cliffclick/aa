package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

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

  @Override public boolean is_mem() { return true; }
  //@Override public TV2 new_tvar(String alloc_site) { return TV2.make_mem(this,alloc_site); }
  @Override public String xstr() { return _tn._name; }
  Node mem() { return in(1); }
  Node ptr() { return in(2); }

  // --------------------------------------------------------------------------
  // Takes in an unaliased piece of memory and Names it: basically sticks a
  // vtable name type in memory.  Unaliased, so the same memory cannot be
  // referred to without the Name.  Error if the memory cannot be proven
  // unaliased.  The Ideal call collapses the Name into the unaliased NewNode.

  // Very similar to a Java '<init>' function.
  public static FunPtrNode convertTypeName( TypeObj tn, Parse badargs, ProjNode ptr ) {
    // The incoming memory type is *exact* and does not have any extra fields.
    // The usual duck typing is "this-or-below", which allows and ignores extra
    // fields.  For Naming - which involves installing a v-table (or any other
    // RTTI) the type is exact at that moment.  Super-type constructors are
    // possible but here the type is exact.

    FunNode fun = (FunNode)Env.GVN.init(new FunNode(AA.DSP_IDX+1).add_def(Env.ALL_CTRL));
    Node rpc    = Env.GVN.init(new ParmNode(CTL_IDX," rpc",fun,Env.ALL_CALL,null));
    Node dsp    = Env.GVN.init(new ParmNode(DSP_IDX,"^"   ,fun,((NewObjNode)ptr.in(0))._tptr,Node.con(ptr._val),null));
    Node mem    = Env.GVN.init(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.ALL_MEM,null));
    Node cvt    = Env.GVN.init(new IntrinsicNode(tn,badargs,fun,mem,dsp));
    RetNode ret = Env.GVN.init(new RetNode(fun,cvt,dsp,rpc,fun));
    // Hook function at the TOP scope, because it may yet have unwired
    // CallEpis which demand memory.  This hook is removed as part of doing
    // the Combo pass which computes a real Call Graph and all escapes.
    Env.TOP._scope.add_def(ret);
    FunPtrNode fptr = (FunPtrNode)Env.GVN.xform(new FunPtrNode(tn._name,ret));
    return fptr;
  }

  // If the input memory is unaliased, fold into the NewNode.
  // If this node does not fold away, the program is in error.
  @Override public Node ideal_reduce() {
    Node mem = mem();
    Node ptr = ptr();
    if( mem instanceof MrgProjNode &&
        mem.in(0)==ptr.in(0) && mem._uses._len==2 ) { // Only self and DefMem users
      TypeMemPtr tptr = (TypeMemPtr) ptr._val;
      int alias = tptr._aliases.abit();
      if( alias > 0 ) {         // Not a mixed set of aliases
        NewObjNode nnn = (NewObjNode)mem.in(0);
        // NewObjNode is well-typed and producing a pointer to memory with the
        // correct type?  Fold into the NewObjNode and remove this Convert.
        TypeTuple tnnn = (TypeTuple) nnn._val;
        Type actual = mem._val.sharptr(tnnn.at(REZ_IDX));
        if( actual instanceof TypeMemPtr ) actual = ((TypeMemPtr)actual)._obj; // Get the struct
        Type formal = _tn.remove_name();
        if( actual.isa(formal) ) { // Actual struct isa formal struct?
          TypeStruct tn = nnn._ts.make_from(_tn._name);
          nnn.set_name(tn);
          nnn.xval(); // Update immediately to preserve monotonicity
          mem.xval();
          return mem;
        }
      }
    }

    // If is of a MemJoin and it can enter the split region, do so.
    if( ptr._val instanceof TypeMemPtr && mem instanceof MemJoinNode && mem._uses._len==1 &&
        ptr instanceof ProjNode && ptr.in(0) instanceof NewNode )
      return ((MemJoinNode)mem).add_alias_below_new(new IntrinsicNode(_tn,_badargs,null,mem,ptr),this);

    return null;
  }

  // Semantics are to extract a TypeObj from mem and ptr, and if there is no
  // aliasing, sharpen the TypeObj to a Type with a name.  We can be correct and
  // conservative by doing nothing.

  // The inputs are a TypeMem and a TypeMemPtr to an unnamed TypeObj.  If the
  // ptr is of the "from" type, we cast a Name to it and produce a pointer to
  // the "to" type, otherwise we get the most conservative "to" type.
  @Override public Type value() {
    Type mem = mem()._val;
    Type ptr = ptr()._val;
    if( !(mem instanceof TypeMem   ) ) return mem.oob(); // Inputs are confused
    if( !(ptr instanceof TypeMemPtr) ) return ptr.oob(); // Inputs are confused
    TypeMem tmem = (TypeMem)mem;
    // Get the Obj from the pointer.
    TypeObj obj = tmem.ld((TypeMemPtr)ptr);
    TypeObj tn = (TypeObj)_tn.remove_name();
    if( !obj.isa(tn       ) ) return tmem; // Inputs not correct from, and node is in-error
    if(  obj.isa(tn.dual()) ) return tmem;
    // Wrap result in Name
    int alias = ((TypeMemPtr)ptr)._aliases.abit();
    TypeObj rez = (TypeObj)obj.set_name(_tn._name);
    return tmem.set(alias,rez);
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live_use(Node def ) {
    if( def==mem() ) return _live;
    return TypeMem.ALIVE;
  }
  @Override BitsAlias escapees() { return ptr().in(0).escapees(); }
  // We must inline and fold away to be correct.  The only allowed caller is the unknown one.
  @Override public ErrMsg err( boolean fast ) {
    if( in(0) instanceof FunNode && in(0).len()==2 && ((FunNode)in(0)).has_unknown_callers() )
      return null;             // No error if only called by the unknown caller
    if( fast ) return ErrMsg.FAST;
    Type ptr = ptr()._val;
    Type mem = mem()._val;
    return ErrMsg.typerr(_badargs,ptr,mem,TypeMemPtr.make(BitsAlias.REC,_tn)); // Did not remove the aliasing
  }

  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewObjNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewObjNode.
  // Passed in a named TypeStruct, and the parent alias.
  public static FunPtrNode convertTypeNameStruct( TypeStruct to, int alias, Parse bad, Env e, ProjNode ptr ) {
    assert to.has_name();
    NewObjNode proto = (NewObjNode)ptr.in(0);

    // Count fields needing an argument.  Final fields are assigned from the
    // prototype object.  Scalar fields get an argument.  TODO: Gather
    // initializers and use them instead of an explicit argument.
    int nargs = AA.ARG_IDX;
    for( TypeFld fld : to.flds() )
      if( fld._t==Type.SCALAR )
        nargs++;

    // Function header
    FunNode fun = (FunNode)Env.GVN.init(new FunNode(nargs).add_def(Env.ALL_CTRL));
    Node rpc    = Env.GVN.init(new ParmNode(CTL_IDX," rpc",fun,Env.ALL_CALL,null));
    Node mem    = Env.GVN.init(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.ALL_MEM,null));

    // Object being constructed
    NewObjNode nnn = new NewObjNode(false,alias,to,null);
    nnn.pop();                  // Drop the display, will be added below
    int nargs2 = AA.ARG_IDX;    // Renumber required params, since some fields will not need a param

    // Fill in the fields
    for( int i=AA.DSP_IDX; i<proto._defs._len; i++ ) {
      TypeFld fld = to.fld_idx(i);
      nnn.add_def( fld._t==Type.SCALAR
                   ? Env.GVN.init(new ParmNode(nargs2++,fld._fld,fun,Env.ALL_PARM,bad))
                   : proto.in(i));
    }
    // Finish and return
    nnn = Env.GVN.init(nnn);
    MrgProjNode mrg = Env.GVN.init(new MrgProjNode(nnn,mem));
    ProjNode pnnn   = Env.GVN.init(new ProjNode(REZ_IDX,nnn));
    RetNode ret     = Env.GVN.init(new RetNode(fun,mrg,pnnn,rpc,fun));
    // Hook function at the TOP scope, because it may yet have unwired
    // CallEpis which demand memory.  This hook is removed as part of doing
    // the Combo pass which computes a real Call Graph and all escapes.
    Env.TOP._scope.add_def(ret);
    FunPtrNode fptr = (FunPtrNode)Env.GVN.xform(new FunPtrNode(to._name,ret));
    return fptr;
  }

}
