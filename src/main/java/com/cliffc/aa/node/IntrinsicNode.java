package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

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
  public static FunPtrNode convertTypeName( TypeObj tn, Parse badargs ) {
    // The incoming memory type is *exact* and does not have any extra fields.
    // The usual duck typing is "this-or-below", which allows and ignores extra
    // fields.  For Naming - which involves installing a v-table (or any other
    // RTTI) the type is exact at that moment.  Super-type constructors are
    // possible but here the type is exact.

    // This function call takes in and returns a plain ptr-to-object.
    // Only after folding together does the name become apparent.
    try(GVNGCM.Build<FunPtrNode> X = Env.GVN.new Build<>()) {
      TypeStruct formals = TypeStruct.args(TypeMemPtr.STRUCT);
      TypeFunSig sig = TypeFunSig.make(formals,TypeMemPtr.make(BitsAlias.RECORD_BITS,tn));
      FunNode fun = X.init2((FunNode)new FunNode(tn._name,sig,-1,false).add_def(Env.FILE._scope));
      assert !fun.is_prim(); // prims use Env.SCP_0 not FILE scope
      Node rpc = X.xform(new ParmNode(CTL_IDX," rpc",fun,Env.ALL_CALL,null));
      Node mem = X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
      Node ptr = X.xform(new ParmNode(ARG_IDX,"x",fun,(ConNode)Node.con(TypeMemPtr.make(BitsAlias.RECORD_BITS,TypeObj.ISUSED)),badargs));
      Node cvt = X.xform(new IntrinsicNode(tn,badargs,fun,mem,ptr));
      RetNode ret = (RetNode)X.xform(new RetNode(fun,cvt,ptr,rpc,fun));
      return (X._ret = X.init2(new FunPtrNode(tn._name,ret)));
    }
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
    if( _keep==0 && ptr._val instanceof TypeMemPtr && mem instanceof MemJoinNode && mem._uses._len==1 &&
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
  @Override public Type value(GVNGCM.Mode opt_mode) {
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
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==mem() ) return _live;
    return TypeMem.ALIVE;
  }
  @Override BitsAlias escapees() { return ptr().in(0).escapees(); }
  //
  @Override public ErrMsg err( boolean fast ) {
    if( fast ) return ErrMsg.FAST;
    Type ptr = ptr()._val;
    Type mem = mem()._val;
    return ErrMsg.typerr(_badargs,ptr,mem,TypeMemPtr.make(BitsAlias.REC,_tn)); // Did not remove the aliasing
  }

  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewObjNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewObjNode.
  // Passed in a named TypeStruct, and the parent alias.
  public static FunPtrNode convertTypeNameStruct( TypeStruct to, int alias, Parse bad ) {
    assert to.has_name() && to.fld_find("^").is_display_ptr(); // Display already
    // Upgrade the type to one with no display for nnn.
    to = to.replace_fld(TypeFld.NO_DISP);
    TypeFunSig sig = TypeFunSig.make(to.remove_name(),to);

    try(GVNGCM.Build<FunPtrNode> X = Env.GVN.new Build<>()) {
      FunNode fun = (FunNode) X.xform(new FunNode(to._name,sig,-1,false).add_def(Env.FILE._scope));
      assert !fun.is_prim(); // prims use Env.SCP_0 not FILE scope
      Node rpc = X.xform(new ParmNode(  0    ," rpc",fun,Env.ALL_CALL,null));
      Node memp= X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
      // Add input edges to the NewNode
      Node nodisp = Node.con(TypeMemPtr.NO_DISP);
      NewObjNode nnn = (NewObjNode)X.add(new NewObjNode(false,alias,to,nodisp));
      while( nnn.len() < to.nargs() ) nnn.add_def(null);
      for( TypeFld fld : to.flds() )
        if( !Util.eq(fld._fld,"^") ) // Display already handled
          nnn.set_def(fld._order,(X.xform(new ParmNode(fld,fun, (ConNode)Node.con(fld._t.simple_ptr()),bad))));
      Node mmem = Env.DEFMEM.make_mem_proj(nnn,memp);
      Node ptr = X.xform(new ProjNode(REZ_IDX, nnn));
      RetNode ret = (RetNode)X.xform(new RetNode(fun,mmem,ptr,rpc,fun));
      return (X._ret=X.init2(new FunPtrNode(to._name,ret)));
    }
  }

}
