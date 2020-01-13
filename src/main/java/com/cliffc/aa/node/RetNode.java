package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.VBitSet;

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
  public FunPtrNode funptr() {
    for( Node use : _uses )
      if( use instanceof FunPtrNode )
        return (FunPtrNode)use;
    return null;
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
  
  @Override public Node ideal(GVNGCM gvn) {
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
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    if( is_copy() ) return all_type();
    Type ctl = gvn.type(ctl()).bound(Type.CTRL);
    Type mem = gvn.type(mem()).bound(TypeMem.ALL_MEM);
    Type val = gvn.type(val()).bound(Type.SCALAR);
    return TypeTuple.make(ctl,mem,val);
  }
  @Override public Type all_type() { return TypeTuple.CALL; }

  // Set of used aliases across all inputs (not StoreNode value, but yes address)
  @Override public VBitSet alias_uses(GVNGCM gvn) {
    // Returns all modified reachable memories plus a return alias.
    // Approximate as reachable from call input.
    
    // Get function input memory type, and reach from the return.
    VBitSet abs = new VBitSet(); // Set of escaping aliases
    Type omem = gvn.type(mem());
    if( !(omem instanceof TypeMem) ) return null; // Wait until types fall
    TypeMem output_mem = (TypeMem)omem;

    // Aliases reachable from output memory and return pointer
    Type tval = gvn.type(val());
    if( tval instanceof TypeMemPtr )
      ((TypeMemPtr)tval).recursive_aliases(abs,output_mem);

    // Aliases reachable from input arguments
    for( Node use : fun()._uses ) {
      Type t = gvn.type(use);
      if( t instanceof TypeMemPtr )
        ((TypeMemPtr)t).recursive_aliases(abs,output_mem);
    }
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
