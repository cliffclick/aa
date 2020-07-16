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
  int _fidx;                 // Shortcut to fidx when the FunNode has collapsed
  int _nargs;                // Replicated from FunNode
  public RetNode( Node ctrl, Node mem, Node val, Node rpc, FunNode fun ) { super(OP_RET,ctrl,mem,val,rpc,fun); _fidx = fun._fidx; _nargs=fun.nargs(); }
  public Node ctl() { return in(0); }
  public Node mem() { return in(1); }
  public Node val() { return in(2); }
  public Node rpc() { return in(3); }
  public FunNode fun() { return (FunNode)in(4); }
  @Override boolean is_mem() { return true; }
  // If this function is not using any displays, then there is a single unique
  // FunPtr.  Otherwise this call is ambiguous, as each execution of the
  // FunPtrNode makes a new display.
  public FunPtrNode funptr() {
    FunPtrNode fpn=null;
    for( Node use : _uses )
      if( use instanceof FunPtrNode ) {
        if( fpn!=null ) return null; // Ambiguous; several displays from the same function
        fpn = (FunPtrNode)use;
      }
    return fpn;                 // Zero (null) or 1 display.
  }
  public int fidx() { return _fidx; }
  @Override public int hashCode() { return super.hashCode()+_fidx; }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _fidx==((RetNode)o)._fidx;
  }

  // Short self name
  @Override String xstr() {
    if( is_dead() ) return "Ret";
    FunNode fun = FunNode.find_fidx(_fidx);
    return "Ret_"+(is_copy() ? "!copy!" : (fun==null ? ""+_fidx : fun.name()));
  }
  // Inline longer name
  @Override public String str() { return in(4) instanceof FunNode ? "Ret"+fun().str() : xstr(); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If control is dead, but the Ret is alive, we're probably only using the
    // FunPtr as a 'gensym'.  Nuke the function body.
    if( !is_copy() && gvn.type(ctl())== Type.XCTRL && !is_prim())
      set_def(4,null,gvn);      // We're a copy now!

    // If no users inlining, wipe out all edges
    if( is_copy() && in(0)!=null ) {
      boolean only_fptr = true;
      for( Node use : _uses )  if( !(use instanceof FunPtrNode) ) { only_fptr=false; break; }
      if( only_fptr ) {           // Only funptr uses, make them all gensyms
        set_def(0,null,gvn);      // No ctrl
        set_def(1,null,gvn); if( is_dead() ) return this; // No mem
        set_def(2,null,gvn);      // No val
        set_def(3,null,gvn);      // No rpc
        set_def(4,null,gvn);      // No fun
        return this;              // Progress
      }
    }
    if( is_copy() ) return null;
    // Collapsed to a constant?  Remove any control interior.
    if( gvn.type(val()).is_con() && ctl()!=fun() && // Profit: can change control and delete function interior
        (gvn.type(mem())==TypeMem.EMPTY || (mem() instanceof ParmNode && mem().in(0)==fun())) ) // Memory has to be trivial also
      return set_def(0,fun(),gvn); // Gut function body
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    if( ctl()==null ) return gvn.self_type(this); // No change if a copy
    TypeTuple TALL = TypeTuple.RET;
    Type ctl = gvn.type(ctl());
    if( ctl != Type.CTRL ) return ctl.oob(TALL);
    Type mem = gvn.type(mem());
    if( !(mem instanceof TypeMem) ) return mem.oob(TALL);
    Type val = gvn.type(val());
    return TypeTuple.make(ctl,mem,val);
  }


  @Override public boolean basic_liveness() { return false; }
  @Override public TypeMem live( GVNGCM gvn) {
    // Pre-GCP, might be used anywhere (still finding CFG)
    return gvn._opt_mode < 2 ? TypeMem.ALLMEM : super.live(gvn);
  }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( def==mem() ) return _live;
    if( def==val() ) return TypeMem.ESCAPE;
    return TypeMem.ALIVE;       // Basic aliveness
  }

  @Override public Node is_copy(GVNGCM gvn, int idx) { throw com.cliffc.aa.AA.unimpl(); }
  boolean is_copy() { return !(in(4) instanceof FunNode) || fun()._fidx != _fidx; }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() {
    return val().is_prim() ? val().op_prec() : -1;
  }

  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }
}
