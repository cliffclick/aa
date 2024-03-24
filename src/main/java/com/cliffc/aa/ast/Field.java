package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.LoadNode;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.TODO;

public class Field extends AST {
  final String _name;

  public Field(String name, AST ptr) {
    super(ptr);
    _name = name;
  }

  // .fld
  @Override public SB str(SB sb) { return _kids.at(0).str(sb).p(".").p(_name); }
  @Override public void nodes( Env e ) {
    _kids.at(0).nodes(e);
    Node ptr = e._scope.rez();
    Node mem = e._scope.mem();
    e._scope.rez(new LoadNode(mem,ptr,_name,false,false,null).init());
  }
}
