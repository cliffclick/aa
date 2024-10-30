package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeNil;
import com.cliffc.aa.type.TypeRPC;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import static com.cliffc.aa.AA.*;

public class Lambda extends ASTVars {
  FunNode _fun;

  public Lambda( Ary<String> vars, AST body ) { super(vars); _kids.push(body); }

  AST body() { return _kids.at(0); }

  int addEdge(int to) { return 0; }

  @Override public SB str(SB sb) {
    sb.p("{ ");
    for( int i=ARG_IDX; i<_vars._len; i++ )
      sb.p(_vars.at(i)).p(" ");
    sb.p("->").nl();
    body().str(sb.ii(1).i()).nl().di(1);
    return sb.ip("}");
  }

  @Override public void nodes( Env outer ) {
    ScopeNode outScope = outer._scope;
    // Build the FunNode header
    _fun = new FunNode(_vars._len).init().keep();

    // Build Parms for system incoming values
    Node rpc = new ParmNode(CTL_IDX,_fun,null,TypeRPC.ALL_CALL ).init();
    Node mem = new ParmNode(MEM_IDX,_fun,null,TypeMem.ALLMEM   ).init();
    Node dsp = new ParmNode(DSP_IDX,_fun,null,outScope.ptr()._tptr).init();
    // Increase scope depth for function body.
    try( Env e = new Env(outer, _fun, _vars._len-DSP_IDX, _fun, mem, dsp,"LAMBDA", null) ) { // Nest an environment for the local vars
      ScopeNode inScope = e._scope;
      // Display is special: the default is simply the outer lexical scope.
      // But here, in a function, the display is actually passed in as a hidden
      // extra argument and replaces the default.
      StructNode frame = inScope.stk();
      // Parms for all arguments
      assert _fun==e._fun && _fun==inScope.ctrl();
      for( int i=ARG_IDX; i<_vars._len; i++ ) { // User parms start
        Node parm = new ParmNode(i,_fun,null,TypeNil.SCALAR).peep();
        frame.add_fld(_vars.at(i),Access.Final,parm,null);
      }

      // Node-ify function body
      body().nodes(e);

      frame.close();

      // Merge normal exit into all early-exit paths
      assert frame.is_closure();
      //rez = merge_exits(rez);
      // Standard return; function control, memory, result, RPC.  Plus a hook
      // to the function for faster access.
      _fun.unkeep();
      RetNode ret = new RetNode(inScope.ctrl(),inScope.mem(),inScope.rez(),rpc,_fun).init();

      // The containing scope - it might be a struct scope, not just a closure scope
      Node frsh;

      if( outScope.stk().is_closure() ) {
        // Take just the prefix of scope variables declared up through now (after
        // sorting for mutual-let-rec); add the mut-let-rec set to the nongens.
        frsh = new PartialScopeFreshNode(outScope).peep();
        // CNC  6/Oct/2024 not sure needed
        // CNC 29/Oct/2024 think needed to stop open cycle; leads to endless expansion
        frsh.addDef(outScope.ptr());
        // TODO: expecting to have to repeat this up-scope
        for( AST par = _par, old = this; par!=null; old = par, par = par._par )
          if( par instanceof LetRec let && old==let.body() && let._frefs != null )
            for( Node fref : let._frefs )
              frsh.addDef(fref);
      } else {
        frsh = outScope.ptr();
      }

      // Make a fat fcn pointer; the frsh is the closure pointer.
      Node code = new FunPtrNode(ret,frsh).peep();

      // Return fat fcn pointer / closure
      outScope.rez(code);
    }
  }

  // All Lambda args are non-generative
  @Override void addNonGen(FreshNode frsh) {
    for( int i=ARG_IDX; i<_vars._len; i++ )
      frsh.addDef(_fun.parm(i));
  }
}
