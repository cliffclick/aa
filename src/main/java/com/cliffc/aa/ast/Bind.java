package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.BindFPNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.SB;

public class Bind extends AST {
  public Bind(AST fun, AST dsp) { super(fun,dsp); }
  @Override public SB str(SB sb) {
    sb.p("bind(");
    _kids.at(0).str(sb).p(",");
    _kids.at(1).str(sb).p(")");
    return sb;
  }
  @Override public void nodes( Env e ) {
    _kids.at(0).nodes(e);
    Node fun = e._scope.rez().keep();
    _kids.at(1).nodes(e);
    Node dsp = e._scope.rez();
    e._scope.rez(new BindFPNode(fun.unkeep(),dsp).peep());
  }
}
