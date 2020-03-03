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
  // If this function is not using any displays, then there is a single unique
  // FunPtr.  Otherwise this call is ambiguous, as each execution of the
  // FunPtrNode makes a new display.
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
    if( is_copy() ) return null;
    // Collapsed to a constant?  Remove any control interior.
    if( gvn.type(val()).is_con() && ctl()!=fun() && // Profit: can change control and delete function interior
        (gvn.type(mem())==TypeMem.EMPTY || (mem() instanceof ParmNode && mem().in(0)==fun())) ) // Memory has to be trivial also
      return set_def(0,fun(),gvn); // Gut function body
    // Something changed (hence we got here), so all wired uses need to re-check.
    // i.e., trivial functions (constant returns or 1-op) might now inline.
    //if( (level&1)==0 && (gvn.type(val()).is_con() || ctl()==fun()) )
    //  gvn.add_work_uses(this);
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    if( is_copy() ) return gvn.self_type(this); // No change if a copy
    TypeTuple TALL = all_type();
    Type ctl = gvn.type(ctl());
    if( ctl != Type.CTRL ) return ctl.above_center() ? TALL.dual() : TALL;
    Type mem = gvn.type(mem());
    if( mem.above(TypeMem.FULL.dual()) ) return TALL.dual();
    if( !(mem.isa(TypeMem.FULL      )) ) return TALL;
    Type val = gvn.type(val());
    if( val.above(Type.XSCALAR) ) return TALL.dual();
    if( !(val.isa(Type. SCALAR))) return TALL;
    return TypeTuple.make(ctl,mem,val);
  }
  @Override public TypeTuple all_type() { return TypeTuple.make(Type.CTRL,TypeMem.FULL,fun()._tf._ret); }

  @Override public Node is_copy(GVNGCM gvn, int idx) { throw com.cliffc.aa.AA.unimpl(); }
  boolean is_copy() { return !(in(4) instanceof FunNode) || fun()._tf.fidx() != _fidx; }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() {
    return val().is_prim() ? val().op_prec() : -1;
  }

  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }
}
