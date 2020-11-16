package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import java.util.Arrays;

import static com.cliffc.aa.AA.*;

// Assert the matching type.  Parse-time error if it does not remove.  Note the
// difference with CastNode: both Nodes always join their input with their
// constant but a TypeNode has to be proven useless and removed before the
// program is type-correct.  A CastNode is always correct from local semantics,
// and the join is non-trivial.
public class AssertNode extends Node {
  private final Type _t;            // Asserted type
  private final Parse _error_parse; // Used for error messages
  public AssertNode( Node mem, Node a, Type t, Parse P ) {
    super(OP_TYPE,null,mem,a);
    assert !(t instanceof TypeFunPtr);
    _t=t;
    _error_parse = P;
  }
  @Override public String xstr() { return "assert:"+_t; }
  Node mem() { return in(1); }
  Node arg() { return in(2); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node arg= arg(), mem = mem();
    Type actual = arg.sharptr(mem);
    if( actual.isa(_t) )
      return arg;
    // If TypeNode check is for a function, it will wrap any incoming function
    // with a new function which does the right arg-checks.  This happens
    // immediately in the Parser and is here to declutter the Parser.
    if( _t instanceof TypeFunSig ) {
      TypeFunSig sig = (TypeFunSig)_t;
      Node[] args = new Node[sig.nargs()];
      FunNode fun = gvn.init((FunNode)(new FunNode(null,sig,-1,false).add_def(Env.ALL_CTRL)));
      fun.set_val(Type.CTRL);
      args[CTL_IDX] = fun;            // Call control
      args[MEM_IDX] = gvn.xform(new ParmNode(MEM_IDX,"mem",fun,TypeMem.MEM,Env.DEFMEM,null));
      args[FUN_IDX] = arg;            // The whole TFP to the call
      for( int i=ARG_IDX; i<sig.nargs(); i++ )  // 1 is memory, 2 is display.
        // All the parms; types in the function signature
        args[i] = gvn.xform(new ParmNode(i,"arg"+i,fun,gvn.con(Type.SCALAR),_error_parse));
      Parse[] badargs = new Parse[sig.nargs()];
      Arrays.fill(badargs,_error_parse);
      Node rpc= gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
      CallNode call = (CallNode)gvn.xform(new CallNode(true,badargs,args));
      Node cepi   = gvn.xform(new CallEpiNode(call,Env.DEFMEM)).keep();
      Node ctl    = gvn.xform(new CProjNode(cepi));
      Node postmem= gvn.xform(new MProjNode(cepi)).keep();
      Node val    = gvn.xform(new  ProjNode(cepi.unhook(),AA.REZ_IDX));
      // Type-check the return also
      Node chk    = gvn.xform(new AssertNode(postmem,val,sig._ret.at(REZ_IDX),_error_parse));
      RetNode ret = (RetNode)gvn.xform(new RetNode(ctl,postmem.unhook(),chk,rpc,fun));
      // Just the Closure when we make a new TFP
      Node clos = gvn.xform(new FP2ClosureNode(arg));
      return gvn.xform(new FunPtrNode(ret,clos));
    }

    // Push TypeNodes 'up' to widen the space they apply to, and hopefully push
    // the type check closer to the source of a conflict.
    Node fun = arg.in(0);
    if( arg instanceof PhiNode &&
        // Not allowed to push up the typing on the unknown arg... because
        // unknown new callers also need the check.

        // TODO: Probably not legit for FunNodes ever, because have to match
        // the CallNode args with the FunNode args.  Or need to add the very
        // same node as the matching call arg.  Alternatively, simplify the
        // double-edge game going on with CG edges.
        //(!(fun instanceof FunNode) || !((FunNode)fun).has_unknown_callers()) ) {
        fun.getClass() == RegionNode.class ) {
      //for( int i=1; i<arg._defs._len; i++ )
      //  gvn.set_def_reg(arg,i,gvn.xform(new TypeNode(_t,arg.in(i),_error_parse)));
      //return arg;               // Remove TypeNode, since completely replaced
      throw AA.unimpl("untested");
    }

    return null;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Node arg = arg();
    Type t1 = arg.val();
    Type t0 = _t.simple_ptr();
    if( t1.isa(t0) ) {
      Type actual = arg.sharptr(mem());
      if( actual.isa(_t) )
        return t1;
    }
    return t1.oob(t0);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==arg() ) return _live;                   // Alive as I am
    // Alive (like normal liveness), plus the address, plus whatever can be
    // reached from the address.
    return ScopeNode.compute_live_mem(mem(),arg());
  }

  // Check TypeNode for being in-error
  @Override public ErrMsg err( boolean fast ) {
    Type arg = arg().val();
    Type mem = mem().val();
    return ErrMsg.asserterr(_error_parse,arg,mem,_t);
  }
}
