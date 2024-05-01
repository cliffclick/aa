package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.DynLoadNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.SB;
import static com.cliffc.aa.AA.TODO;

public class DynField extends AST {
  public DynField( AST ptr, AST dyn ) { super(ptr,dyn); }
  @Override public SB str(SB sb) { return _kids.at(0).str(sb).p("._"); }
  @Override public void nodes( Env e ) {
    _kids.at(0).nodes(e);
    Node mem = e._scope.mem().keep();
    Node ptr = e._scope.rez().keep();
    _kids.at(1).nodes(e);
    Node dyn = e._scope.rez();
    e._scope.rez(new DynLoadNode(mem.unkeep(),ptr.unkeep(),dyn,null).init());
  }
}
