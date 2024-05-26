package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.node.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.*;

public abstract class ASTVars extends AST {
  final Ary<String> _vars;

  public ASTVars( Ary<String> vars ) { super(); _vars = vars;}

  // Used to find mutual let rec cycles
  abstract int addEdge(int to);

  // Add non-generative edges to a Fresh
  abstract void addNonGen(FreshNode frsh);

  int find(String var) { return _vars.find(var); }
}
