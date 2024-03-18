package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.DefDynTableNode;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.TODO;

public class Root extends AST {

  public Root( AST prog ) { super(prog); }

  @Override public SB str(SB sb) { return _str(sb); }

  @Override public void nodes( Env e ) {
    // Print the program as Nodes
    e._scope.stk().add_fld("$dyn",Access.Final,new DefDynTableNode().init(),null);
    _kids.at(0).nodes(e);
  }
}
