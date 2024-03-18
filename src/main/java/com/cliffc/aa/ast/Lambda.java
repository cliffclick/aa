package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.node.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.*;

public class Lambda extends AST {
  final Ary<String> _ids;

  public Lambda( Ary<String> ids, AST body ) { super(body); _ids = ids;}

  AST body() { return _kids.at(0); }

  @Override public SB str(SB sb) {
    sb.ip("{ ");
    for( int i=ARG_IDX+1; i<_ids._len; i++ )
      sb.p(_ids.at(i)).p(" ");
    sb.p("->").nl().ii(1);
    body().str(sb);
    return sb.di(1).ip("}").nl();
  }

  @Override public void nodes( Env outer ) {
    ScopeNode outScope = outer._scope;
    // Build the FunNode header
    FunNode fun = new FunNode(_ids._len).init().keep();

    // Build Parms for system incoming values
    Node rpc = new ParmNode(CTL_IDX,fun,null,TypeRPC.ALL_CALL ).init();
    Node mem = new ParmNode(MEM_IDX,fun,null,TypeMem.ALLMEM   ).init();
    Node dsp = new ParmNode(DSP_IDX,fun,null,outScope.ptr()._tptr).init();
    // Increase scope depth for function body.
    try( Env e = new Env(outer, fun, _ids._len-DSP_IDX, fun, mem, dsp, null) ) { // Nest an environment for the local vars
      ScopeNode inScope = e._scope;
      // Display is special: the default is simply the outer lexical scope.
      // But here, in a function, the display is actually passed in as a hidden
      // extra argument and replaces the default.
      StructNode frame = inScope.stk();
      // Parms for all arguments
      assert fun==e._fun && fun==inScope.ctrl();
      for( int i=ARG_IDX; i<_ids._len; i++ ) { // User parms start
        Node parm = new ParmNode(i,fun,null,TypeNil.SCALAR).peep();
        frame.add_fld(_ids.at(i),Access.Final,parm,null);
      }

      // Node-ify function body
      body().nodes(e);

      frame.close();

      // Merge normal exit into all early-exit paths
      assert frame.is_closure();
      //rez = merge_exits(rez);
      // Standard return; function control, memory, result, RPC.  Plus a hook
      // to the function for faster access.
      fun.unkeep();
      RetNode ret = new RetNode(inScope.ctrl(),inScope.mem(),inScope.rez(),fun.parm(CTL_IDX),fun).init();

      Node fptr = new FunPtrNode(ret).peep();
      // Anonymous functions early-bind.  Functions in structs become "methods" and late-bind.
      outScope.set_rez(outScope.stk().is_closure() ? new BindFPNode(fptr,outScope.ptr()).peep() : fptr);
    }
  }
}
