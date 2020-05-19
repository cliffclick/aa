package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import java.util.Arrays;

// Assert the matching type.  Parse-time error if it does not remove.  Note the
// difference with CastNode: both Nodes always join their input with their
// constant but a TypeNode has to be proven useless and removed before the
// program is type-correct.  A CastNode is always correct from local semantics,
// and the join is non-trivial.
public class TypeNode extends Node {
  private final Type _t;            // Asserted type
  private final Parse _error_parse; // Used for error messages
  public TypeNode( Node mem, Node a, Type t, Parse P ) {
    super(OP_TYPE,null,mem,a);
    assert !(t instanceof TypeFunPtr);
    _t=t;
    _error_parse = P;
  }
  @Override String xstr() { return "assert:"+_t; }
  Node mem() { return in(1); }
  Node arg() { return in(2); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node arg= arg(), mem = mem();
    Type at = gvn.sharptr(arg,mem);
    if( at.isa(_t) ) return arg;
    // If TypeNode check is for a function, it will wrap any incoming function
    // with a new function which does the right arg-checks.  This happens
    // immediately in the Parser and is here to declutter the Parser.
    if( _t instanceof TypeFunSig ) {
      TypeFunSig sig = (TypeFunSig)_t;
      Node[] args = new Node[sig.nargs()-1/*not display*/+/*+ctrl+mem+tfp+all args*/3];
      FunNode fun = gvn.init((FunNode)(new FunNode(null,sig,-1).add_def(Env.ALL_CTRL)));
      args[0] = fun;            // Call control
      args[1] = mem = gvn.xform(new ParmNode(-2,"mem",fun,TypeMem.MEM,Env.DEFMEM,null)).keep();
      args[2] = arg;            // The whole TFP to the call
      for( int i=1; i<sig.nargs(); i++ )  // First is display
        // All the parms; types in the function signature
        args[i+2] = gvn.xform(new ParmNode(i,"arg"+i,fun,gvn.con(Type.SCALAR),null));
      Parse[] badargs = new Parse[sig.nargs()];
      Arrays.fill(badargs,_error_parse);
      Node rpc= gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
      CallNode call = (CallNode)gvn.xform(new CallNode(true,badargs,args));
      Node cepi   = gvn.xform(new CallEpiNode(call,Env.DEFMEM)).keep();
      Node ctl    = gvn.xform(new CProjNode(cepi,0));
      Node postmem= gvn.xform(new MProjNode(cepi,1)).keep();
      Node val    = gvn.xform(new  ProjNode(cepi.unhook(),2));
      // Type-check the return also
      Node chk    = gvn.xform(new  TypeNode(mem.unhook(),val,sig._ret,_error_parse)); 
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
      throw com.cliffc.aa.AA.unimpl("untested");
    }

    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Node arg = arg();
    Type t1 = gvn.type(arg);
    Type t2 = t1.bound(_t.simple_ptr());
    return t2;
  }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( _live == TypeMem.DEAD ) return TypeMem.DEAD; // Am dead, so nothing extra is alive.
    // Alive (like normal liveness), plus the address, plus whatever can be
    // reached from the address.
    return ScopeNode.compute_live_mem(gvn,TypeMem.UNUSED,mem(),arg());
  }

  // Check TypeNode for being in-error
  @Override public String err(GVNGCM gvn) { return _error_parse.typerr(gvn.type(arg()),mem(),_t); }
}
