package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// See CallNode comments.  The RetNode gathers {control (function exits or
// not), memory, value, rpc, fun}, and sits at the end of a function.  The RPC
// dictates which calls can be reached from here.  The Fun is used to rapidly
// find the FunNode, as a SESE region shortcut.  A FunPtrNode points to this
// Ret, and is used for all function-pointer uses.  Otherwise only CallEpis
// point to a Ret representing wired calls.

public final class RetNode extends Node {
  int _fidx;                    // Shortcut to fidx when the FunNode has collapsed
  public RetNode( Node ctrl, Node mem, Node val, Node rpc, FunNode fun ) { super(OP_RET,ctrl,mem,val,rpc,fun); _fidx = fun.fidx();}
  public Node ctl() { return in(0); }
  public Node mem() { return in(1); }
  public Node val() { return in(2); }
  public Node rpc() { return in(3); }
  public FunNode fun() { return (FunNode)in(4); }
  // If this function is not using any closures, then there is a single unique
  // FunPtr.  Otherwise this call is ambiguous, as each execution of the
  // FunPtrNode makes a new closure.
  public FunPtrNode funptr() {
    FunPtrNode fpn=null;
    for( Node use : _uses )
      if( use instanceof FunPtrNode ) {
        assert fpn==null;
        fpn = (FunPtrNode)use;
      }
    return fpn;
  }
  public int fidx() { return _fidx; }
  // Short self name
  @Override String xstr() {
    if( is_dead() ) return "Ret";
    FunNode fun = FunNode.find_fidx(_fidx);
    return "Ret_"+(is_copy() ? "!copy!" : (fun==null ? ""+_fidx : fun.name()));
  }
  // Inline longer name
  @Override public String str() { return in(4) instanceof FunNode ? "Ret"+fun().str() : xstr(); }

  // RetNode lost a use.  If losing the last wired call, might disappear
  // (degrade to a unique symbol supporting ld,st,equality but not execution).
  @Override public boolean ideal_impacted_by_losing_uses(GVNGCM gvn, Node dead) {
    return dead instanceof CallEpiNode;
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If is_copy, wipe out inputs rpc & fun, but leave ctrl,mem,val for users to inline
    if( is_copy() && in(4)!=null ) {
      set_def(3,null,gvn);      // No rpc
      set_def(4,null,gvn);      // No fun
      return this;              // Progress
    }
    // If no users inlining, wipe out all edges
    if( is_copy() && in(0)!=null && _uses._len==1 && _uses.at(0) instanceof FunPtrNode ) {
      set_def(0,null,gvn);      // No ctrl
      set_def(1,null,gvn);      // No mem
      set_def(2,null,gvn);      // No val
      return this;              // Progress
    }
    // Collapsed to a constant?  Remove any control interior.
    if( gvn.type(val()).is_con() && ctl()!=fun() && // Profit: can change control and delete function interior
        (gvn.type(mem())==TypeMem.EMPTY || (mem() instanceof ParmNode && mem().in(0)==fun())) ) // Memory has to be trivial also
      return set_def(0,fun(),gvn); // Gut function body
    // Something changed (hence we got here), so all wired uses need to re-check.
    // i.e., trivial functions (constant returns or 1-op) might now inline.
    if( (level&1)==0 && (gvn.type(val()).is_con() || ctl()==fun()) )
      gvn.add_work_uses(this);
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    if( is_copy() ) return all_type();
    Type ctl = gvn.type(ctl());
    if( ctl != Type.CTRL ) return ctl.above_center() ? TypeTuple.XRET : TypeTuple.RET;
    Type mem = gvn.type(mem());
    if( mem.above(TypeMem.FULL.dual()) ) return TypeTuple.XRET;
    if( !(mem.isa(TypeMem.FULL      )) ) return TypeTuple. RET;
    Type val = gvn.type(val());
    if( val.above(Type.XSCALAR) ) return TypeTuple.XRET;
    if( !(val.isa(Type. SCALAR))) return TypeTuple. RET;
    // If function is collapsing, do not change types (yet).  The Parm Memory
    // might be gone, and the trimming gets confused.
    FunNode fun = fun();
    if( !fun.has_unknown_callers() && fun._defs._len==2 && !fun.is_forward_ref() )
      return gvn.self_type(this);
    mem = ((TypeMem)mem).trim_to_alias(alias_uses(gvn));
    return TypeTuple.make(ctl,mem,val);
  }
  @Override public Type all_type() { return TypeTuple.RET; }

  // Only return memory of aliases that conservatively MAY have been modified
  // and callers MAY be able to see.  This can be, e.g. ALL of memory, but we
  // try to exclude both obviously not modified memory (which includes
  // unreachable memory) and obviously not visible to caller (which includes
  // our local closure if it does not escape).
  //
  // Depends on the returned value type and memory type, and the structure of
  // the Parms to the Function.
  @Override public BitsAlias alias_uses(GVNGCM gvn) {
    // Walk up a chain of pure functions, to see if we see any modifications to
    // memory.  Allows to skip a chain of primitives.
    Node mem = mem();    // Return memory
    Node cepi;  Type tcepi;
    while( mem instanceof MProjNode && (cepi=mem.in(0)) instanceof CallEpiNode &&
           (tcepi=gvn.type(cepi)) instanceof TypeTuple &&
           ((TypeTuple)tcepi).at(3)==TypeMem.EMPTY &&
            !((CallEpiNode)cepi).is_copy() )
            mem = ((CallNode)cepi.in(0)).mem();

    // Get reasonable memory type
    Type omem = gvn.type(mem);
    if( !(omem instanceof TypeMem) ) return BitsAlias.NZERO; // Wait until types get more stable
    TypeMem output_mem = (TypeMem)omem;

    BitsAlias abs = BitsAlias.EMPTY; // Set of escaping aliases
    // Closures reachable from this function escape, because we assume the
    // function body modifies all closure variables.
    FunNode fun = fun();
    if( !fun.is_parm(mem) ) {  // Shortcut: Skip if no memory effects at all
      MemMergeNode mmem = mem instanceof MemMergeNode ? ((MemMergeNode)mem) : null;
      for( int alias : fun._closure_aliases )
        // If memory effect is strange, or this alias is not directly from the
        // function entry, then assume it is modified and part of the result state.
        if( mmem == null || !fun.is_parm(mmem.alias2node(alias)) )
          abs = output_mem.recursive_aliases(abs,alias);
      if( abs.test(1) ) return BitsAlias.NZERO; // Shortcut
    }

    // Aliases reachable from output memory and return pointer
    Type tval = gvn.type(val());
    abs = tval.recursive_aliases(abs,output_mem);
    if( abs.test(1) ) return BitsAlias.NZERO; // Shortcut
    // Check for escaping the local closure up and out.
    // TODO: Only escape if function ptrs are from interior functions.
    if( tval.isa(TypeFunPtr.GENERIC_FUNPTR) )
      abs = output_mem.recursive_aliases(abs,fun._my_closure_alias);

    // Aliases reachable from input arguments, and are modified.
    for( Node use : fun()._uses )
      if( use instanceof ParmNode )
        abs = gvn.type(use).recursive_aliases(abs,output_mem);
     assert !abs.test(0);
    return abs;
  }

  @Override public Node is_copy(GVNGCM gvn, int idx) { throw com.cliffc.aa.AA.unimpl(); }
  boolean is_copy() { return !(in(4) instanceof FunNode) || fun()._tf.fidx() != _fidx; }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() {
    return val()._uid < GVNGCM._INIT0_CNT ? val().op_prec() : -1;
  }

  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }
}
