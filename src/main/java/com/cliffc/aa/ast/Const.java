package com.cliffc.aa.ast;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.node.ConNode;
import com.cliffc.aa.Env;


public class Const extends AST {
  public final Type _t;
  public Const( Type t ) { _t = t; }
  @Override public SB str(SB sb) {
    return sb.p(_t.toString());
  }

  @Override public void nodes( Env e ) {
    e._scope.rez( new ConNode(_t) );
  }
}
