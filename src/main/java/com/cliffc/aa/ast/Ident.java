package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.TODO;


public class Ident extends AST {
  final String _name;
  public Ident( String name ) { _name = name; }
  @Override public SB str(SB sb) { return sb.p(_name); }
  @Override public void nodes( Env e ) {
    Node x = e.lookup(_name);
    if( x==null )
      throw TODO();
    e._scope.rez(e.lookup(_name));
  }
}
