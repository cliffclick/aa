package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.*;


public class Call extends AST {
  // 0 CTL - null
  // 1 MEM - null
  // 2 DSP - null
  // 3 DYN - $dyn
  // 4 ARGS- ...
  // n FCN -
  public Call( AST...   kids ) { super(kids); }
  public Call( Ary<AST> kids ) { super(kids); }

  // fcn( . . args)
  @Override public SB str(SB sb) {
    AST fcn = _kids.last();
    fcn.str(sb);
    sb.p("(  ");
    for( int i=ARG_IDX+1; i<_kids._len-1; i++ )
      _kids.at(i).str(sb).p(", ");
    return sb.unchar(2).p(")");
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
    scope.rez (new  ProjNode(cepi.unkeep(),REZ_IDX).peep());
  }
}
