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
  public TypeNode( Node mem, Node a, Type t, Parse P ) { super(OP_TYPE,null,mem,a); _t=t; _error_parse = P; }
  @Override String xstr() { return "assert:"+_t; }
  Node mem() { return in(1); }
  Node arg() { return in(2); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node arg = arg(), mem;
    Type at = gvn.sharptr(arg,mem());
    if( at.isa(_t) ) return arg;
    // If TypeNode check is for a function pointer, it will wrap any incoming
    // function with a new function which does the right arg-checks.  This
    // happens immediately in the Parser and is here to declutter the Parser.
    if( _t instanceof TypeFunPtr/*signature not fidxs*/ ) {
      TypeFunPtr tfp = (TypeFunPtr)_t;
      Type[] targs = tfp._args._ts;
      Node[] args = new Node[targs.length-2/*not return nor display*/+/*+ctrl+mem+tfp+all args*/3];
      FunNode fun = gvn.init((FunNode)(new FunNode(tfp._args._flds,targs).add_def(Env.ALL_CTRL)));
      args[0] = fun;            // Call control
      args[1] = mem = gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM),null)).keep();
      args[2] = arg;            // The whole TFP to the call
      for( int i=2; i<targs.length; i++ ) { // First is return, 2nd is display
        // All the parms, with types
        Node parm = gvn.xform(new ParmNode(i,"arg"+i,fun,gvn.con(Type.SCALAR),null));
        args[i+1] = gvn.xform(new TypeNode(mem,parm,targs[i],_error_parse));
      }
      Parse[] badargs = new Parse[targs.length];
      Arrays.fill(badargs,_error_parse);
      Node rpc= gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
      CallNode call = (CallNode)gvn.xform(new CallNode(true,badargs,args));
      Node cepi   = gvn.xform(new CallEpiNode(call)).keep();
      Node ctl    = gvn.xform(new CProjNode(cepi,0));
      Node postmem= gvn.xform(new MProjNode(cepi,1)).keep();
      Node val    = gvn.xform(new  ProjNode(cepi.unhook(),2));
      Node chk    = gvn.xform(new  TypeNode(mem.unhook(),val,tfp.ret(),_error_parse)); // Type-check the return also
      RetNode ret = (RetNode)gvn.xform(new RetNode(ctl,postmem.unhook(),chk,rpc,fun));
      // Just the Closure when we make a new TFP
      Node clos = gvn.xform(new FP2ClosureNode(arg));
      return gvn.xform(new FunPtrNode(ret,clos,(TypeMemPtr)gvn.type(clos)));
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
    Type t = gvn.type(arg);
    if( mem() == null || !(t instanceof TypeMemPtr) || !(_t instanceof TypeMemPtr) )
      return t.bound(_t).simple_ptr();
    Type tmem = gvn.type(mem());
    Type t2 = t.sharpen(tmem);
    if( _t.dual().isa(t2) && t2.isa(_t) ) return t.simple_ptr();
    return (tmem.above_center() ? _t.dual() : _t).simple_ptr();
  }
  @Override public Type all_type() { return Type.SCALAR; }
  // Check TypeNode for being in-error
  @Override public String err(GVNGCM gvn) { return _error_parse.typerr(gvn.type(arg()),mem(),_t); }
}
