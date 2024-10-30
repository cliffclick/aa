package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.DefDynTableNode;
import com.cliffc.aa.node.FreshNode;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

public class Root extends ASTVars {
  public DefDynTableNode _dyn;

  public Root( AST prog ) {
    super(new Ary<>(new String[]{"$dyn"}));
    _kids.push(prog);
  }

  @Override public SB str(SB sb) { return _str(sb); }

  @Override public void nodes( Env e ) {
    // Print the program as Nodes.
    // Always an initial Dyn-Table
    _dyn = (DefDynTableNode)e._par._scope.stk().in("$dyn");
    _kids.at(0).nodes(e);
  }

  // No-op for mutual-let-rec detection
  @Override int addEdge(int to) { return 0; }

  // Add non-generative $dyn edge to a Fresh
  // Same as EXE, root does not have "$dyn" as Fresh, just a plain argument.
  // CNC 29/Oct/2024
  // - No  addDef breaks something
  // - Yes addDef breaks testResolve2.aa but EXE testOver18.aa passes
  @Override void addNonGen(FreshNode frsh) { frsh.addDef(_dyn); }
}
