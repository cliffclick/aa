package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Assert the matching type.  Parse-time error if it does not remove.  Note the
// difference with CastNode: both Nodes always join their input with their
// constant but an Assert has to be proven useless and removed before the
// program is type-correct.  A CastNode is always correct from local semantics,
// and the join is non-trivial.
public class AssertNode extends Node {
  final Type _t;                    // Asserted type
  Parse _bad;                       // Used for error messages
  public AssertNode( Node mem, Node arg, Type t, Parse bad ) {
    super(OP_TYPE,null,mem,arg);
    assert !(t instanceof TypeFunPtr);
    _t=t;
    _bad = bad;
  }
  @Override public String xstr() { return "assert:"+_t; }
  Node mem() { return in(MEM_IDX); }
  Node arg() { return in(REZ_IDX); }

  @Override public Type value() {
    Node arg = arg();
    Type targ = arg._val;
    // Asserts can be handed function signatures instead of function pointers.
    Type t2 = _t instanceof TypeTuple tt && tt.is_fun_sig() ? tt.as_tfp() : _t;
    if( targ.isa(t2) ) return targ;
    
    Type t0 = t2.simple_ptr();
    if( targ.isa(t0) ) {
      Type actual = arg.sharptr(mem());
      if( actual.isa(t2) )  return targ;
    }
    // Value is capped to the assert value.
    return targ.meet(t0).join(t0);
  }

  @Override public Type live_use( Node def ) {
    if( def==arg() ) return _live; // Alive as I am
    // Memory is alive for errors
    Type t = arg()._val;    
    return t instanceof TypeMemPtr tmp
      ? TypeMem.make(tmp._aliases,TypeStruct.ISUSED)
      : TypeMem.ANYMEM;
  }

  @Override public boolean assert_live(Type live) {
    return live.getClass() == arg()._live.getClass();
  }

  @Override public Node ideal_reduce() {
    Type actual = arg()._val;
    Node mem = mem();
    // Never a pointer to sharpen, drop memory
    if( mem!=null &&
        !(actual instanceof TypeMemPtr) && // No pointer in actual
        !actual.above_center() )           // Cannot fall to a pointer
      return set_def(1,null);
    // If have a memory, sharpen
    if( mem!=null )
      actual = mem._val.sharptr(actual);
    // If ISA, remove assert
    return actual.isa(_t) ? arg() : null;
  }
  
  @Override public Node ideal_grow() {
    Node arg= arg();
    // If the AssertNode check is for a function, wrap any incoming function
    // with a new function which does the right arg-checks.  This happens
    // immediately in the Parser and is here to declutter the Parser.
    if( _t instanceof TypeTuple tt && tt.is_fun_sig() ) {
      try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
        int nargs = tt.nargs();
        FunNode fun = new FunNode(nargs);
        int fidx = fun.push();  // Hook to keep alive
        fun = (FunNode)X.xform(fun);
        Node rpc = X.xform(new ParmNode(0,fun,null,TypeRPC.ALL_CALL));
        // All the parms; types in the function signature
        Node[] args = new Node[nargs+1];
        args[CTL_IDX] = fun;            // Call control
        args[MEM_IDX] = X.xform(new ParmNode(MEM_IDX,fun,null,TypeMem.ALLMEM));
        args[DSP_IDX] = X.xform(new ParmNode(DSP_IDX,fun,null,TypeNil.SCALAR));
        for( int i=ARG_IDX; i<nargs; i++ ) {
          Node parm = X.xform(new ParmNode(i,fun,null,TypeNil.SCALAR));
          args[i] = X.xform(new AssertNode(args[MEM_IDX],parm,tt.at(i),_bad));
        }
        args[nargs] = arg();
          
        CallNode call = (CallNode)X.xform(new CallNode(true,null,args));
        Node cepi   = X.xform(new CallEpiNode(call));
        Node ctl    = X.xform(new CProjNode(cepi));
        Node postmem= X.xform(new MProjNode(cepi));
        Node val    = X.xform(new  ProjNode(cepi,AA.REZ_IDX));
        // Type-check the return also
        Node chk    = X.xform(new AssertNode(postmem,val,tt.ret(),_bad));
        RetNode ret = (RetNode)X.xform(new RetNode(ctl,postmem,chk,rpc,fun));
        // Just the same Closure when we make a new TFP
        Node.pop(fidx);
        return (X._ret=X.xform(new FunPtrNode(null,ret)));
      }
    }

    // Push TypeNodes 'up' to widen the space they apply to, and hopefully push
    // the type check closer to the source of a conflict.
    Node fun = arg.len()>0 ? arg.in(0) : null;
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

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    TV3 tv3 = TV3.from_flow(_t);
    arg().set_tvar().unify(tv3,false);
    return tv3;
  }
  

  // Check TypeNode for being in-error
  @Override public ErrMsg err( boolean fast ) {
    Type arg = arg()._val;
    if( mem()!=null )
      arg = mem()._val.sharptr(arg);
    return ErrMsg.asserterr(_bad,arg, _t);
  }
}
