package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.*;


public class Call extends AST {
  public Call( AST... kids ) { super(kids); }

  // fcn( . . args)
  @Override public SB str(SB sb) {
    AST fcn = _kids.last();
    fcn.str(sb);
    assert sb.was_nl();
    sb.unchar(2).p("(").nl().ii(1);
    for( int i=ARG_IDX+1; i<_kids._len-1; i++ )
      _kids.at(i).str(sb);
    return sb.di(1).ip(")").nl();
  }

  @Override public void nodes( Env e ) {
    ScopeNode scope = e._scope;
    // Collect all arguments; must keep them alive
    Node[] args = new Node[_kids._len];
    for( int i=ARG_IDX; i<_kids._len; i++ ) {
      _kids.at(i).nodes(e);
      args[i] = scope.rez().keep();
    }
    args[CTL_IDX] = scope.ctrl();
    args[MEM_IDX] = scope.mem();
    args[DSP_IDX] = scope.ptr();
    for( int i=ARG_IDX; i<_kids._len; i++ )
      args[i].unkeep();
    // Make the Call
    CallNode call = (CallNode)new CallNode(true,null,args).peep();
    Node cepi = new CallEpiNode(call).peep().keep();
    scope.ctrl(new CProjNode(cepi).peep());
    scope.mem (new MProjNode(cepi).peep()); // Return memory from all called functions
    Node r = new ProjNode(cepi.unkeep(),REZ_IDX).peep();
    scope.set_rez(r);
  }
}
