package com.cliffc.aa.ast;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.AFieldNode;

import static com.cliffc.aa.AA.TODO;


public class AField extends AST {
  public AField( AST dyn ) { super(dyn); }
  @Override public SB str(SB sb) { return _str(sb); }
  @Override public void nodes( Env e ) {
    _kids.at(0).nodes(e);
    Node dyn = e._scope.rez();
    e._scope.set_rez(new AFieldNode(dyn).peep());
  }
}
