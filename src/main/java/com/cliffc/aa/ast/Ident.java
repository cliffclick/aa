package com.cliffc.aa.ast;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.Env;
import static com.cliffc.aa.AA.TODO;


public class Ident extends AST {
  final String _name;
  public Ident( String name ) { _name = name; }
  @Override public SB str(SB sb) {
    return sb.ip(_name).nl();
  }

  @Override public void nodes( Env e ) {
    e._scope.set_rez(e.lookup(_name));
  }
}
