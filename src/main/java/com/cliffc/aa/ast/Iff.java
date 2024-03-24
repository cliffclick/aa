package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.TODO;

public class Iff extends AST {
  public Iff(AST pred, AST t, AST f) { super(pred,t,f); }

  @Override public SB str(SB sb) {
    _kids.at(0).str(sb).p(" ? ");
    _kids.at(1).str(sb).p(" : ");
    _kids.at(2).str(sb);
    return sb;
  }
  @Override public void nodes( Env e ) {
    ScopeNode scope = e._scope;
    _kids.at(0).nodes(e);
    Node mem = scope.mem();
    IfNode iff = new IfNode(scope.ctrl(),scope.rez()).init();

    scope.ctrl(new CProjNode(iff,1).init());
    _kids.at(1).nodes(e);
    Node tctrl = scope.ctrl().keep();
    Node tmem  = scope.mem ().keep();
    Node trez  = scope.rez ().keep();

    scope.ctrl(new CProjNode(iff,0).init());
    _kids.at(2).nodes(e);
    Node fctrl = scope.ctrl();
    Node fmem  = scope.mem();
    Node frez  = scope.rez();

    RegionNode r = new RegionNode(null,tctrl.unkeep(),fctrl).init();
    PhiNode prez = new PhiNode(TypeNil.SCALAR,null,r,trez.unkeep(),frez).init();
    PhiNode pmem = new PhiNode(TypeMem.ALLMEM,null,r,tmem.unkeep(),fmem).init();
    scope.ctrl(r);
    scope.mem (pmem);
    scope.rez (prez);
  }
}
