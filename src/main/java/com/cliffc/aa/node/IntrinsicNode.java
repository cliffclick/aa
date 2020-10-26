package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

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

  @Override
  public boolean is_mem() { return true; }
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
    TypeStruct formals = TypeStruct.make_args(TypeStruct.ts(TypeFunPtr.NO_DISP,TypeMemPtr.STRUCT));
    TypeFunSig sig = TypeFunSig.make(formals,TypeMemPtr.make(BitsAlias.RECORD_BITS,tn));
    FunNode fun = (FunNode) gvn.xform(new FunNode(tn._name,sig,-1,false).add_def(Env.ALL_CTRL));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node mem = gvn.xform(new ParmNode(-2,"mem",fun,TypeMem.MEM,Env.DEFMEM,null));
    Node ptr = gvn.xform(new ParmNode( 1,"ptr",fun,gvn.con(TypeMemPtr.ISUSED),badargs));
    Node cvt = gvn.xform(new IntrinsicNode(tn,badargs,fun,mem,ptr));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,cvt,ptr,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret,gvn.con(TypeFunPtr.NO_DISP)));
  }

  // If the input memory is unaliased, fold into the NewNode.
  // If this node does not fold away, the program is in error.
  @Override public Node ideal(GVNGCM gvn, int level) {
    Node mem = mem();
    Node ptr = ptr();

    // If is of a MemJoin and it can enter the split region, do so.
    if( _keep==0 && ptr.val() instanceof TypeMemPtr && mem instanceof MemJoinNode && mem._uses._len==1 &&
        ptr instanceof ProjNode && ptr.in(0) instanceof NewNode )
      return ((MemJoinNode)mem).add_alias_below_new(gvn,new IntrinsicNode(_tn,_badargs,null,mem,ptr),this);

    if( mem instanceof MrgProjNode &&
        mem.in(0)==ptr.in(0) && mem._uses._len==2 ) { // Only self and DefMem users
      TypeMemPtr tptr = (TypeMemPtr) ptr.val();
      int alias = tptr._aliases.abit();
      if( alias > 0 ) {         // Not a mixed set of aliases
        NewObjNode nnn = (NewObjNode)mem.in(0);
        // NewObjNode is well-typed and producing a pointer to memory with the
        // correct type?  Fold into the NewObjNode and remove this Convert.
        TypeTuple tnnn = (TypeTuple) nnn.val();
        Type actual = mem.val().sharptr(tnnn.at(1));
        if( actual instanceof TypeMemPtr ) actual = ((TypeMemPtr)actual)._obj; // Get the struct
        Type formal = _tn.remove_name();
        if( actual.isa(formal) ) { // Actual struct isa formal struct?
          TypeStruct tn = nnn._ts.make_from(_tn._name);
          nnn.set_name(tn);
          nnn.xval(gvn._opt_mode); // Update immediately to preserve monotonicity
          mem.xval(gvn._opt_mode);
          return mem;
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
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type mem = mem().val();
    Type ptr = ptr().val();
    if( !(mem instanceof TypeMem   ) ) return mem.oob(); // Inputs are confused
    if( !(ptr instanceof TypeMemPtr) ) return ptr.oob(); // Inputs are confused
    TypeMem tmem = (TypeMem)mem;
    // Get the Obj from the pointer.
    int alias = ((TypeMemPtr)ptr)._aliases.abit();
    TypeObj obj = tmem.ld((TypeMemPtr)ptr);
    TypeObj tn = (TypeObj)_tn.remove_name();
    if( !obj.isa(tn       ) ) return tmem; // Inputs not correct from, and node is in-error
    if(  obj.isa(tn.dual()) ) return tmem;
    // Wrap result in Name
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
    Type ptr = ptr().val();
    Type mem = mem().val();
    return ErrMsg.typerr(_badargs,ptr,mem,TypeMemPtr.make(BitsAlias.REC,_tn)); // Did not remove the aliasing
  }

  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list.  Just a NewObjNode but the
  // result is a named type.  Same as convertTypeName on an unaliased NewObjNode.
  // Passed in a named TypeStruct, and the parent alias.
  public static FunPtrNode convertTypeNameStruct( TypeStruct to, int alias, GVNGCM gvn, Parse bad ) {
    assert to.has_name();
    assert Util.eq(to._flds[0],"^"); // Display already
    assert to.fmod(0)==TypeStruct.FFNL; // Display is final
    // Upgrade the type to one with no display for nnn.
    to = to.set_fld(0,TypeMemPtr.NO_DISP,TypeStruct.FFNL);
    // Formal is unnamed, and this function adds the name.
    TypeStruct formals = to.remove_name();
    TypeFunSig sig = TypeFunSig.make(formals,TypeMemPtr.make(BitsAlias.make0(alias),to));
    FunNode fun = (FunNode) gvn.xform(new FunNode(to._name,sig,-1,false).add_def(Env.ALL_CTRL));
    Node rpc = gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    Node memp= gvn.init(new ParmNode(-2,"mem",fun,TypeMem.MEM,Env.DEFMEM,null));
    // Add input edges to the NewNode
    ConNode nodisp = gvn.con(TypeMemPtr.NO_DISP);
    NewObjNode nnn = new NewObjNode(false,alias,to,nodisp).keep();
    for( int i=1; i<to._ts.length; i++ ) { // Display in 0, fields in 1+
      String argx = to._flds[i];
      if( TypeStruct.fldBot(argx) ) argx = null;
      nnn.add_def(gvn.xform(new ParmNode(i,argx,fun, gvn.con(to._ts[i].simple_ptr()),bad)));
    }
    gvn.init(nnn);
    Node mmem = Env.DEFMEM.make_mem_proj(gvn,nnn.unhook(),memp);
    Node ptr = gvn.xform(new  ProjNode(1, nnn));
    RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mmem,ptr,rpc,fun));
    return (FunPtrNode)gvn.xform(new FunPtrNode(ret,nodisp));
  }

}
