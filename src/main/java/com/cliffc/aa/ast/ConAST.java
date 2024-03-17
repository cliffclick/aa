package com.cliffc.aa.ast;

import com.cliffc.aa.type.Type;

public class ConAST extends AST {
  public final Type _t;
  public ConAST( Type t ) { _t = t; }
  @Override public String toString() { return _t.toString(); }
}
