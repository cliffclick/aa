package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
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
  private final Env _env;           // Lexical scope
  public AssertNode( Node mem, Node a, Type t, Parse P, Env e ) {
    super(OP_TYPE,null,mem,a);
    assert !(t instanceof TypeFunPtr);
    _t=t;
    _error_parse = P;
    _env = e;
  }
  @Override public String xstr() { return "assert:"+_t; }
  Node mem() { return in(MEM_IDX); }
  Node arg() { return in(REZ_IDX); }

  @Override public Node ideal_reduce() {
    Type actual = arg().sharptr(mem());
    return actual.isa(_t) ? arg() : null;
  }
  @Override public Node ideal_grow() {
    Node arg= arg();
    // If TypeNode check is for a function, it will wrap any incoming function
    // with a new function which does the right arg-checks.  This happens
    // immediately in the Parser and is here to declutter the Parser.
    if( _t instanceof TypeFunSig ) {
      TypeFunSig sig = (TypeFunSig)_t;
      try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
        X.add(this);
        Node[] args = new Node[sig.nargs()+1];
        FunNode fun = (FunNode)X.init(new FunNode(null,sig,-1,false).add_def(Env.ALL_CTRL));
        fun._val = Type.CTRL;
        args[CTL_IDX] = fun;            // Call control
        args[MEM_IDX] = X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
        args[DSP_IDX] = X.xform(new ParmNode(DSP_IDX,"^"   ,fun,(ConNode)Node.con(TypeMemPtr.DISP_SIMPLE),_error_parse));
        for( TypeFld fld : sig._formals.flds() )
          if( fld._order >= ARG_IDX )
            // All the parms; types in the function signature
            args[fld._order] = X.xform(new ParmNode(fld,fun,(ConNode)Node.con(Type.SCALAR),_error_parse));
        args[sig.nargs()] = arg;        // The whole TFP to the call
        Parse[] badargs = new Parse[sig.nargs()];
        Arrays.fill(badargs,_error_parse);
        Node rpc= X.xform(new ParmNode(0," rpc",fun,Env.ALL_CALL,null));
        CallNode call = (CallNode)X.xform(new CallNode(true,badargs,args));
        Node cepi   = X.xform(new CallEpiNode(/*TODO: Suspect need to carry a prior Env thru*/call,Env.DEFMEM));
        Node ctl    = X.xform(new CProjNode(cepi));
        Node postmem= X.xform(new MProjNode(cepi));
        Node val    = X.xform(new  ProjNode(cepi,AA.REZ_IDX));
        // Type-check the return also
        Node chk    = X.xform(new AssertNode(postmem,val,sig._ret.at(REZ_IDX),_error_parse,_env));
        RetNode ret = (RetNode)X.xform(new RetNode(ctl,postmem,chk,rpc,fun));
        // Just the same Closure when we make a new TFP
        return (X._ret=X.xform(new FunPtrNode(ret,arg)));
      }
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
    Type t1 = arg._val;
    Type t0 = _t.simple_ptr();
    if( t1.isa(t0) ) {
      Type actual = arg.sharptr(mem());
      if( actual.isa(_t) )
        return t1;
    }
    // Value is capped to the assert value.
    return t1.oob(t0);
  }
  @Override public void add_work_use_extra(Work work, Node chg) {
    if( ideal_reduce()!=null )
      Env.GVN.add_reduce(this);
  }

  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==arg() ) return _live;                   // Alive as I am
    // Alive (like normal liveness), plus the address, plus whatever can be
    // reached from the address.
    return ScopeNode.compute_live_mem(null,mem(),arg());
  }

  // Check TypeNode for being in-error
  @Override public ErrMsg err( boolean fast ) {
    Type arg = arg()._val;
    Type mem = mem()._val;
    return ErrMsg.asserterr(_error_parse,arg,mem,_t);
  }
}
